package sproof.syntax

import munit.FunSuite
import sproof.core.*

class ElaboratorSuite extends FunSuite:

  private def parseAndElab(input: String): Either[ElabError, ElabResult] =
    Parser.parseProgram(input).left.map(e => ElabError(e)).flatMap(Elaborator.elaborate)

  // ===== Inductive type elaboration =====

  test("elaborate Nat inductive") {
    val input = """inductive Nat { case zero: Nat case succ(n: Nat): Nat }"""
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    val natDef = elab.env.lookupInd("Nat")
    assert(natDef.isDefined, "Nat should be in global env")
    assertEquals(natDef.get.name, "Nat")
    assertEquals(natDef.get.ctors.length, 2)
    assertEquals(natDef.get.ctors(0).name, "zero")
    assertEquals(natDef.get.ctors(0).argTpes, Nil)
    assertEquals(natDef.get.ctors(1).name, "succ")
  }

  test("elaborate Nat succ has one argument") {
    val input = """inductive Nat { case zero: Nat case succ(n: Nat): Nat }"""
    val result = parseAndElab(input)
    val elab = result.toOption.get
    val succCtor = elab.env.lookupInd("Nat").get.ctors(1)
    assertEquals(succCtor.argTpes.length, 1)
  }

  test("elaborate empty inductive") {
    val input = """inductive Empty { }"""
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    val emptyDef = elab.env.lookupInd("Empty")
    assert(emptyDef.isDefined, "Empty should be in global env")
    assertEquals(emptyDef.get.ctors, Nil)
  }

  // ===== Function elaboration =====

  test("elaborate identity function") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def id(x: Nat): Nat = x""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    assert(elab.defs.contains("id"), "id should be in defs")
    // After Fix wrapping: Fix("id", Pi(x:Nat,Nat), Lam("x", Nat, Var(0)))
    // The Lam body Var(0) = x (the lambda binding) ✓
    val Term.Fix("id", _, Term.Lam("x", _, Term.Var(0))) = elab.defs("id"): @unchecked
  }

  test("elaborate function with two params") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def const(x: Nat, y: Nat): Nat = x""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    // nameEnv = ["y","x"], so x=Var(1), y=Var(0).
    // After Fix wrapping: Fix("const", ..., Lam("x", _, Lam("y", _, Var(1))))
    val Term.Fix("const", _, Term.Lam("x", _, Term.Lam("y", _, Term.Var(1)))) =
      elab.defs("const"): @unchecked
  }

  test("elaborate function with constructor call") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def zero_const(x: Nat): Nat = Nat.zero""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    // After Fix wrapping: Fix("zero_const", ..., Lam("x", _, Con("zero","Nat",Nil)))
    val Term.Fix("zero_const", _, Term.Lam("x", _, Term.Con("zero", "Nat", Nil))) =
      elab.defs("zero_const"): @unchecked
  }

  test("elaborate function with match") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def isZero(n: Nat): Nat {
        |  match n {
        |    case Nat.zero => Nat.zero
        |    case Nat.succ(k) => Nat.zero
        |  }
        |}""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    // After Fix wrapping: Fix("isZero", ..., Lam("n", _, Mat(...)))
    val body = elab.defs("isZero")
    assert(body.isInstanceOf[Term.Fix], s"Expected Fix, got $body")
    val Term.Fix(_, _, Term.Lam(_, _, mat)) = body: @unchecked
    assert(mat.isInstanceOf[Term.Mat], s"Expected Mat inside Fix, got $mat")
  }

  test("elaborate match cases have correct bindings count") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def isZero(n: Nat): Nat {
        |  match n {
        |    case Nat.zero => Nat.zero
        |    case Nat.succ(k) => Nat.zero
        |  }
        |}""".stripMargin
    val result = parseAndElab(input)
    val elab = result.toOption.get
    val Term.Fix(_, _, Term.Lam(_, _, Term.Mat(_, cases, _))) = elab.defs("isZero"): @unchecked
    assertEquals(cases(0).bindings, 0)
    assertEquals(cases(1).bindings, 1)
  }

  // ===== Defspec elaboration =====

  test("elaborate defspec preserves proof") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |defspec refl(n: Nat): n = n { by trivial }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    assert(elab.defspecs.contains("refl"), "refl should be in defspecs")
    val (_, _, proof) = elab.defspecs("refl")
    val SProof.SBy(STactic.STrivial) = proof: @unchecked
  }

  test("elaborate defspec with induction preserves proof") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def plus(n: Nat, m: Nat): Nat {
        |  match n {
        |    case Nat.zero => m
        |    case Nat.succ(k) => Nat.succ(plus(k, m))
        |  }
        |}
        |defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
        |  by induction n {
        |    case zero => trivial
        |    case succ k ih => simplify [plus, ih]
        |  }
        |}""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    assert(elab.defspecs.contains("plus_zero"), "plus_zero should be in defspecs")
  }

  // ===== Error cases =====

  test("elaborate duplicate inductive name") {
    val input =
      """inductive Nat { case zero: Nat }
        |inductive Nat { case one: Nat }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Should fail on duplicate inductive name")
  }

  test("elaborate duplicate def name") {
    val input =
      """inductive Nat { case zero: Nat }
        |def f(x: Nat): Nat = x
        |def f(y: Nat): Nat = y""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Should fail on duplicate def name")
  }

  test("elaborate unresolved type variable") {
    val input = """def f(x: Unknown): Unknown = x"""
    val result = parseAndElab(input)
    assert(result.isLeft, "Should fail on unresolved type")
  }

  test("elaborate unresolved constructor") {
    val input =
      """inductive Nat { case zero: Nat }
        |def f(x: Nat): Nat = Foo.bar""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Should fail on unresolved constructor")
  }

  test("elaborate function with recursive call") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def plus(n: Nat, m: Nat): Nat {
        |  match n {
        |    case Nat.zero => m
        |    case Nat.succ(k) => Nat.succ(plus(k, m))
        |  }
        |}""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    assert(elab.defs.contains("plus"), "plus should be in defs")
    // After Fix wrapping: Fix("plus", Pi(n:Nat, Pi(m:Nat, Nat)), Lam("n", ..., Lam("m", ..., Mat(...))))
    val body = elab.defs("plus")
    assert(body.isInstanceOf[Term.Fix], s"Expected Fix, got $body")
    val Term.Fix("plus", _, Term.Lam("n", _, Term.Lam("m", _, mat))) = body: @unchecked
    assert(mat.isInstanceOf[Term.Mat], s"Expected Mat inside Fix+Lam, got $mat")
  }

  // ===== Global env state =====

  test("elaborate builds cumulative global env") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |inductive Bool { case true: Bool case false: Bool }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    assert(elab.env.lookupInd("Nat").isDefined, "Nat should be in env")
    assert(elab.env.lookupInd("Bool").isDefined, "Bool should be in env")
  }

  // ===== Structure elaboration =====

  test("elaborate structure desugars to inductive with mk constructor") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Wrap { value: Nat }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    val wrapInd = elab.env.lookupInd("Wrap")
    assert(wrapInd.isDefined, "Wrap inductive should be in env")
    assertEquals(wrapInd.get.ctors.length, 1)
    assertEquals(wrapInd.get.ctors(0).name, "mk")
    assertEquals(wrapInd.get.ctors(0).argTpes.length, 1)
  }

  test("elaborate structure registers in structures map") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Wrap { value: Nat }""".stripMargin
    val result = parseAndElab(input)
    val elab = result.toOption.get
    val structDef = elab.env.lookupStruct("Wrap")
    assert(structDef.isDefined, "Wrap should be in structures map")
    assertEquals(structDef.get.fields.length, 1)
    assertEquals(structDef.get.fields(0)._1, "value")
  }

  test("elaborate structure generates field accessor def") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Wrap { value: Nat }""".stripMargin
    val result = parseAndElab(input)
    val elab = result.toOption.get
    val accessor = elab.env.lookupDef("Wrap_value")
    assert(accessor.isDefined, "Wrap_value accessor should be in defs")
  }

  test("elaborate structure with two fields generates two accessors") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Pair { fst: Nat  snd: Nat }""".stripMargin
    val result = parseAndElab(input)
    val elab = result.toOption.get
    assert(elab.env.lookupDef("Pair_fst").isDefined, "Pair_fst accessor should exist")
    assert(elab.env.lookupDef("Pair_snd").isDefined, "Pair_snd accessor should exist")
  }

  test("elaborate structure duplicate name returns Left") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Foo { x: Nat }
        |structure Foo { y: Nat }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Duplicate structure name should fail")
  }

  // ===== Instance elaboration =====

  test("elaborate instance desugars to constant def") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Wrap { value: Nat }
        |instance wrapZero: Wrap { value = Nat.zero }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    val inst = elab.env.lookupDef("wrapZero")
    assert(inst.isDefined, "wrapZero def should be in env")
    // body should be Con("mk", "Wrap", [Con("zero","Nat",[])])
    val Term.Con("mk", "Wrap", args) = inst.get.body: @unchecked
    assertEquals(args.length, 1)
    assertEquals(args(0), Term.Con("zero", "Nat", Nil))
  }

  test("elaborate instance with wrong struct name returns Left") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |instance bad: NonExistentStruct { value = Nat.zero }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Unknown struct name should fail")
  }

  test("elaborate instance with missing field returns Left") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Pair { fst: Nat  snd: Nat }
        |instance partial: Pair { fst = Nat.zero }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Missing field in instance should fail")
  }

  test("elaborate instance with extra field returns Left") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |structure Wrap { value: Nat }
        |instance bad: Wrap { value = Nat.zero  extra = Nat.zero }""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Extra field in instance should fail")
  }

  // ===== Operator elaboration =====

  test("elaborate operator registers in operators map") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def plus(n: Nat, m: Nat): Nat { match n { case Nat.zero => m case Nat.succ(k) => Nat.succ(plus(k, m)) } }
        |operator (x: Nat) + (y: Nat): Nat = plus(x, y)""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    val opFn = elab.env.lookupOperator("+")
    assert(opFn.isDefined, "+ operator should be registered")
  }

  test("elaborate operator creates a def") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def plus(n: Nat, m: Nat): Nat { match n { case Nat.zero => m case Nat.succ(k) => Nat.succ(plus(k, m)) } }
        |operator (x: Nat) + (y: Nat): Nat = plus(x, y)""".stripMargin
    val result = parseAndElab(input)
    val elab = result.toOption.get
    val opFn = elab.env.lookupOperator("+").get
    assert(elab.env.lookupDef(opFn).isDefined, "operator def should exist in env")
  }

  test("elaborate duplicate operator symbol returns Left") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def plus(n: Nat, m: Nat): Nat { match n { case Nat.zero => m case Nat.succ(k) => Nat.succ(plus(k, m)) } }
        |operator (x: Nat) + (y: Nat): Nat = plus(x, y)
        |operator (x: Nat) + (y: Nat): Nat = plus(x, y)""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Duplicate operator symbol should fail")
  }

  // ===== Infix expression elaboration =====

  test("elaborate infix expression uses registered operator") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def plus(n: Nat, m: Nat): Nat { match n { case Nat.zero => m case Nat.succ(k) => Nat.succ(plus(k, m)) } }
        |operator (x: Nat) + (y: Nat): Nat = plus(x, y)
        |def addZero(n: Nat): Nat = n + Nat.zero""".stripMargin
    val result = parseAndElab(input)
    assert(result.isRight, s"Elaboration failed: $result")
    val elab = result.toOption.get
    assert(elab.defs.contains("addZero"), "addZero should be elaborated")
  }

  test("elaborate infix with unknown operator returns Left") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def addZero(n: Nat): Nat = n + Nat.zero""".stripMargin
    val result = parseAndElab(input)
    assert(result.isLeft, "Unregistered operator should fail")
  }
