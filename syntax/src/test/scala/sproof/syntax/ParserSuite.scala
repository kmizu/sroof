package sproof.syntax

import munit.FunSuite

class ParserSuite extends FunSuite:

  // ===== Type parsing =====

  test("parse simple type variable") {
    val result = Parser.parseType("Nat")
    assertEquals(result, Right(SType.STVar("Nat")))
  }

  test("parse arrow type") {
    val result = Parser.parseType("Nat -> Nat")
    assertEquals(result, Right(SType.STArrow(SType.STVar("Nat"), SType.STVar("Nat"))))
  }

  test("parse arrow type is right-associative") {
    val result = Parser.parseType("A -> B -> C")
    assertEquals(result, Right(
      SType.STArrow(SType.STVar("A"), SType.STArrow(SType.STVar("B"), SType.STVar("C")))
    ))
  }

  test("parse Pi type") {
    val result = Parser.parseType("Pi(x: A, B)")
    assertEquals(result, Right(SType.STPi("x", SType.STVar("A"), SType.STVar("B"))))
  }

  test("parse Type (universe 0)") {
    val result = Parser.parseType("Type")
    assertEquals(result, Right(SType.STUni(0)))
  }

  test("parse Type0") {
    val result = Parser.parseType("Type0")
    assertEquals(result, Right(SType.STUni(0)))
  }

  test("parse Type1") {
    val result = Parser.parseType("Type1")
    assertEquals(result, Right(SType.STUni(1)))
  }

  test("parse type application") {
    val result = Parser.parseType("List(A)")
    assertEquals(result, Right(SType.STApp(SType.STVar("List"), SType.STVar("A"))))
  }

  test("parse parenthesized type") {
    val result = Parser.parseType("(Nat -> Nat) -> Nat")
    assertEquals(result, Right(
      SType.STArrow(
        SType.STArrow(SType.STVar("Nat"), SType.STVar("Nat")),
        SType.STVar("Nat"),
      )
    ))
  }

  // ===== Expression parsing =====

  test("parse variable expression") {
    val result = Parser.parseExpr("x")
    assertEquals(result, Right(SExpr.SEVar("x")))
  }

  test("parse function application") {
    val result = Parser.parseExpr("f(a, b)")
    assertEquals(result, Right(SExpr.SEApp(SExpr.SEVar("f"), List(SExpr.SEVar("a"), SExpr.SEVar("b")))))
  }

  test("parse constructor no args") {
    val result = Parser.parseExpr("Nat.zero")
    assertEquals(result, Right(SExpr.SECon("Nat", "zero", Nil)))
  }

  test("parse constructor with args") {
    val result = Parser.parseExpr("Nat.succ(n)")
    assertEquals(result, Right(SExpr.SECon("Nat", "succ", List(SExpr.SEVar("n")))))
  }

  test("parse match expression") {
    val input = "match n { case Nat.zero => m case Nat.succ(k) => Nat.succ(plus(k, m)) }"
    val result = Parser.parseExpr(input)
    assert(result.isRight, s"Parse failed: $result")
    val SExpr.SEMatch(scrutinee, cases) = result.toOption.get: @unchecked
    assertEquals(scrutinee, SExpr.SEVar("n"))
    assertEquals(cases.length, 2)
    assertEquals(cases(0).ctor, "Nat.zero")
    assertEquals(cases(0).bindings, Nil)
    assertEquals(cases(1).ctor, "Nat.succ")
    assertEquals(cases(1).bindings, List("k"))
  }

  test("parse lambda expression") {
    val result = Parser.parseExpr("fun (x: Nat) => x")
    assert(result.isRight, s"Parse failed: $result")
    val SExpr.SELam(params, body) = result.toOption.get: @unchecked
    assertEquals(params, List(SParam("x", SType.STVar("Nat"))))
    assertEquals(body, SExpr.SEVar("x"))
  }

  // ===== Declaration parsing =====

  test("parse inductive Nat") {
    val input = """inductive Nat { case zero: Nat case succ(n: Nat): Nat }"""
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SInductive(name, params, ctors) = result.toOption.get: @unchecked
    assertEquals(name, "Nat")
    assertEquals(params, Nil)
    assertEquals(ctors.length, 2)
    assertEquals(ctors(0).name, "zero")
    assertEquals(ctors(0).argParams, Nil)
    assertEquals(ctors(0).retTpe, SType.STVar("Nat"))
    assertEquals(ctors(1).name, "succ")
    assertEquals(ctors(1).argParams, List(SParam("n", SType.STVar("Nat"))))
    assertEquals(ctors(1).retTpe, SType.STVar("Nat"))
  }

  test("parse inductive with parameters") {
    val input = """inductive List(A: Type) { case nil: List(A) case cons(head: A, tail: List(A)): List(A) }"""
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SInductive(name, params, ctors) = result.toOption.get: @unchecked
    assertEquals(name, "List")
    assertEquals(params, List(SParam("A", SType.STUni(0))))
    assertEquals(ctors.length, 2)
  }

  test("parse def with equals body") {
    val input = """def id(x: Nat): Nat = x"""
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SDef(name, params, retTpe, body) = result.toOption.get: @unchecked
    assertEquals(name, "id")
    assertEquals(params, List(SParam("x", SType.STVar("Nat"))))
    assertEquals(retTpe, SType.STVar("Nat"))
    assertEquals(body, SExpr.SEVar("x"))
  }

  test("parse def with block body") {
    val input =
      """def plus(n: Nat, m: Nat): Nat {
        |  match n {
        |    case Nat.zero => m
        |    case Nat.succ(k) => Nat.succ(plus(k, m))
        |  }
        |}""".stripMargin
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SDef(name, params, retTpe, body) = result.toOption.get: @unchecked
    assertEquals(name, "plus")
    assertEquals(params.length, 2)
    assert(body.isInstanceOf[SExpr.SEMatch])
  }

  test("parse defspec with trivial") {
    val input = """defspec refl(n: Nat): n = n program = { by trivial }"""
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SDefspec(name, params, prop, proof) = result.toOption.get: @unchecked
    assertEquals(name, "refl")
    assertEquals(params, List(SParam("n", SType.STVar("Nat"))))
    val SProof.SBy(tactic) = proof: @unchecked
    assertEquals(tactic, STactic.STrivial)
  }

  test("parse defspec with induction") {
    val input =
      """defspec plus_zero(n: Nat): plus(n, Nat.zero) = n program = {
        |  by induction n {
        |    case zero => trivial
        |    case succ k ih => simplify [plus, ih]
        |  }
        |}""".stripMargin
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SDefspec(_, _, _, proof) = result.toOption.get: @unchecked
    val SProof.SBy(STactic.SInduction(varName, cases)) = proof: @unchecked
    assertEquals(varName, "n")
    assertEquals(cases.length, 2)
    assertEquals(cases(0).ctorName, "zero")
    assertEquals(cases(0).tactic, STactic.STrivial)
    assertEquals(cases(1).ctorName, "succ")
    assertEquals(cases(1).extraBindings, List("k", "ih"))
    val STactic.SSimplify(lemmas) = cases(1).tactic: @unchecked
    assertEquals(lemmas, List("plus", "ih"))
  }

  // ===== Tactic parsing =====

  test("parse tactic trivial") {
    val result = Parser.parseTactic("trivial")
    assertEquals(result, Right(STactic.STrivial))
  }

  test("parse tactic triv") {
    val result = Parser.parseTactic("triv")
    assertEquals(result, Right(STactic.STriv))
  }

  test("parse tactic assume") {
    val result = Parser.parseTactic("assume x y")
    assertEquals(result, Right(STactic.SAssume(List("x", "y"))))
  }

  test("parse tactic apply") {
    val result = Parser.parseTactic("apply f(x)")
    assert(result.isRight, s"Parse failed: $result")
    val STactic.SApply(expr) = result.toOption.get: @unchecked
    assertEquals(expr, SExpr.SEApp(SExpr.SEVar("f"), List(SExpr.SEVar("x"))))
  }

  test("parse tactic simplify") {
    val result = Parser.parseTactic("simplify [plus, ih]")
    assertEquals(result, Right(STactic.SSimplify(List("plus", "ih"))))
  }

  test("parse tactic simp") {
    val result = Parser.parseTactic("simp [f]")
    assertEquals(result, Right(STactic.SSimp(List("f"))))
  }

  test("parse tactic simp without lemmas") {
    val result = Parser.parseTactic("simp")
    assertEquals(result, Right(STactic.SSimp(Nil)))
  }

  test("parse tactic sorry") {
    val result = Parser.parseTactic("sorry")
    assertEquals(result, Right(STactic.SSorry))
  }

  test("parse tactic induction") {
    val input = "induction n { case zero => triv case succ k ih => sorry }"
    val result = Parser.parseTactic(input)
    assert(result.isRight, s"Parse failed: $result")
    val STactic.SInduction(varName, cases) = result.toOption.get: @unchecked
    assertEquals(varName, "n")
    assertEquals(cases.length, 2)
    assertEquals(cases(0).ctorName, "zero")
    assertEquals(cases(0).extraBindings, Nil)
    assertEquals(cases(0).tactic, STactic.STriv)
    assertEquals(cases(1).ctorName, "succ")
    assertEquals(cases(1).extraBindings, List("k", "ih"))
    assertEquals(cases(1).tactic, STactic.SSorry)
  }

  // ===== Program parsing (multiple declarations) =====

  test("parse multiple declarations") {
    val input =
      """inductive Nat { case zero: Nat case succ(n: Nat): Nat }
        |def id(x: Nat): Nat = x""".stripMargin
    val result = Parser.parseProgram(input)
    assert(result.isRight, s"Parse failed: $result")
    assertEquals(result.toOption.get.length, 2)
  }

  // ===== Equality expression in defspec =====

  test("parse defspec proposition as equality type") {
    // The proposition "plus(n, Nat.zero) = n" is an equality type
    val input = """defspec test(n: Nat): plus(n, Nat.zero) = n program = { by sorry }"""
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
  }

  // ===== Edge cases =====

  test("parse empty inductive (no ctors)") {
    val input = """inductive Empty { }"""
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
    val SDecl.SInductive(name, _, ctors) = result.toOption.get: @unchecked
    assertEquals(name, "Empty")
    assertEquals(ctors, Nil)
  }

  test("parse nested constructor application") {
    val result = Parser.parseExpr("Nat.succ(Nat.succ(Nat.zero))")
    assert(result.isRight, s"Parse failed: $result")
    val SExpr.SECon(_, _, args) = result.toOption.get: @unchecked
    assertEquals(args.length, 1)
    assert(args(0).isInstanceOf[SExpr.SECon], "expected nested SECon")
  }

  test("invalid syntax returns Left") {
    val result = Parser.parseDecl("not a valid declaration")
    assert(result.isLeft, "Expected parse error for invalid input")
  }

  test("parse simplify with empty brackets") {
    val result = Parser.parseTactic("simplify []")
    assertEquals(result, Right(STactic.SSimplify(Nil)))
  }

  test("parse comments are ignored") {
    val input =
      """// this is a comment
        |def id(x: Nat): Nat = x""".stripMargin
    val result = Parser.parseDecl(input)
    assert(result.isRight, s"Parse failed: $result")
  }

  test("parse tactic apply with simple variable") {
    val result = Parser.parseTactic("apply x")
    assert(result.isRight, s"Parse failed: $result")
    val STactic.SApply(expr) = result.toOption.get: @unchecked
    assertEquals(expr, SExpr.SEVar("x"))
  }
