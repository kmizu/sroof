package sproof.extract

import munit.FunSuite
import sproof.core.{Term, GlobalEnv, IndDef, CtorDef, DefEntry, Param, Ctor}

class ExtractorSuite extends FunSuite:

  // ---- shared fixtures ----

  /** Nat inductive definition (mirrors GlobalEnv.natDef). */
  val natInd: Term = Term.Ind("Nat", Nil, Nil)

  val natDef: IndDef = IndDef(
    name     = "Nat",
    params   = Nil,
    ctors    = List(
      CtorDef("zero", Nil),
      CtorDef("succ", List(natInd)),
    ),
    universe = 0,
  )

  // ---- extractInductive ----

  test("extract Nat enum produces correct Scala 3 enum") {
    val result = Extractor.extractInductive(natDef)
    assert(result.contains("enum Nat:"), s"expected 'enum Nat:', got:\n$result")
    assert(result.contains("case Zero"),  s"expected 'case Zero', got:\n$result")
    assert(result.contains("case Succ"), s"expected 'case Succ', got:\n$result")
  }

  test("extract empty inductive produces Empty case") {
    val emptyDef = IndDef("Void", Nil, Nil, 0)
    val result   = Extractor.extractInductive(emptyDef)
    assert(result.contains("enum Void:"), s"expected 'enum Void:', got:\n$result")
    assert(result.contains("case Empty"),  s"expected 'case Empty', got:\n$result")
  }

  test("extract Bool enum with two nullary constructors") {
    val boolDef = IndDef(
      name     = "Bool",
      params   = Nil,
      ctors    = List(CtorDef("false", Nil), CtorDef("true", Nil)),
      universe = 0,
    )
    val result = Extractor.extractInductive(boolDef)
    assert(result.contains("enum Bool:"),  s"got:\n$result")
    assert(result.contains("case False"), s"got:\n$result")
    assert(result.contains("case True"),  s"got:\n$result")
  }

  // ---- termToScalaType ----

  test("termToScalaType: Uni is erased to Any") {
    assertEquals(Extractor.termToScalaType(Term.Uni(0)), "Any")
    assertEquals(Extractor.termToScalaType(Term.Uni(2)), "Any")
  }

  test("termToScalaType: Ind yields type name") {
    assertEquals(Extractor.termToScalaType(Term.Ind("Nat", Nil, Nil)), "Nat")
  }

  test("termToScalaType: non-dependent Pi becomes arrow type") {
    // Pi("_", Nat, Nat) where Var(0) doesn't occur free in cod → Nat => Nat
    val t = Term.Pi("_", natInd, natInd)
    assertEquals(Extractor.termToScalaType(t), "Nat => Nat")
  }

  // ---- termToScalaExpr ----

  test("termToScalaExpr: Var resolves from ctx") {
    val result = Extractor.termToScalaExpr(Term.Var(0), List("x", "y"))
    assertEquals(result, "x")
  }

  test("termToScalaExpr: Var falls back when ctx too short") {
    val result = Extractor.termToScalaExpr(Term.Var(5), List("x"))
    assertEquals(result, "_v5")
  }

  test("termToScalaExpr: Con with no args produces fully-qualified name") {
    val result = Extractor.termToScalaExpr(Term.Con("zero", "Nat", Nil))
    assertEquals(result, "Nat.Zero")
  }

  test("termToScalaExpr: Con with args produces constructor call") {
    val inner  = Term.Con("zero", "Nat", Nil)
    val result = Extractor.termToScalaExpr(Term.Con("succ", "Nat", List(inner)))
    assertEquals(result, "Nat.Succ(Nat.Zero)")
  }

  test("termToScalaExpr: Lam produces lambda expression") {
    // λx:Nat. x  →  (x => x)
    val lam    = Term.Lam("x", natInd, Term.Var(0))
    val result = Extractor.termToScalaExpr(lam)
    assertEquals(result, "(x => x)")
  }

  test("termToScalaExpr: nested Lam resolves De Bruijn correctly") {
    // λx:Nat. λy:Nat. x  — outer binder should be Var(1) in body
    val lam    = Term.Lam("x", natInd, Term.Lam("y", natInd, Term.Var(1)))
    val result = Extractor.termToScalaExpr(lam)
    assertEquals(result, "(x => (y => x))")
  }

  test("termToScalaExpr: Let produces val binding") {
    // let z = Zero in z  →  { val z = Nat.Zero; z }
    val t      = Term.Let("z", natInd, Term.Con("zero", "Nat", Nil), Term.Var(0))
    val result = Extractor.termToScalaExpr(t)
    assertEquals(result, "{ val z = Nat.Zero; z }")
  }

  test("termToScalaExpr: match with zero and succ cases") {
    // match n { zero => zero | succ(k) => k }
    val cases = List(
      sproof.core.MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      sproof.core.MatchCase("succ", 1, Term.Var(0)),  // Var(0) = k
    )
    val mat    = Term.Mat(Term.Var(0), cases, natInd)
    val result = Extractor.termToScalaExpr(mat, List("n"))
    assert(result.contains("n match"), s"expected 'n match', got:\n$result")
    assert(result.contains("case _.Zero"),  s"expected 'case _.Zero', got:\n$result")
    assert(result.contains("case _.Succ"), s"expected 'case _.Succ', got:\n$result")
  }

  // ---- extractDef ----

  test("extract identity function: def id(x: Nat): Nat = x") {
    val tpe  = Term.Pi("x", natInd, natInd)
    val body = Term.Lam("x", natInd, Term.Var(0))
    val result = Extractor.extractDef("id", tpe, body)
    assert(result.startsWith("def id"), s"expected 'def id...', got:\n$result")
    assert(result.contains("(x: Nat)"),   s"expected '(x: Nat)', got:\n$result")
    assert(result.contains(": Nat ="),     s"expected ': Nat =', got:\n$result")
    assert(result.endsWith("= x"),         s"expected to end with '= x', got:\n$result")
  }

  // ---- extractDefspec ----

  test("extract defspec with no params produces Unit def") {
    val result = Extractor.extractDefspec("myTheorem", Nil)
    assertEquals(result, "def myTheorem: Unit = ()")
  }

  test("extract defspec with params produces typed Unit def") {
    val params = List(("n", natInd))
    val result = Extractor.extractDefspec("myTheorem", params)
    assert(result.contains("(n: Nat)"), s"got:\n$result")
    assert(result.contains(": Unit = ()"), s"got:\n$result")
  }

  // ---- extractProgram ----

  test("extractProgram includes inductive and def sections") {
    val env = GlobalEnv.withNat.addDef(
      DefEntry(
        name = "zero",
        tpe  = natInd,
        body = Term.Con("zero", "Nat", Nil),
      )
    )
    val result = Extractor.extractProgram(env)
    assert(result.contains("enum Nat:"),   s"expected enum Nat, got:\n$result")
    assert(result.contains("def zero"),    s"expected def zero, got:\n$result")
  }

  test("termToScalaExpr: Meta becomes ???") {
    val result = Extractor.termToScalaExpr(Term.Meta(42))
    assertEquals(result, "???")
  }
