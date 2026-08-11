package sroof.extract

import munit.FunSuite
import sroof.core.{Term, GlobalEnv, IndDef, CtorDef, DefEntry, Param, Ctor}

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
      sroof.core.MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      sroof.core.MatchCase("succ", 1, Term.Var(0)),  // Var(0) = k
    )
    val mat    = Term.Mat(Term.Var(0), cases, natInd)
    val result = Extractor.termToScalaExpr(mat, List("n"))
    assert(result.contains("n match"), s"expected 'n match', got:\n$result")
    // This used to require `case _.Zero`, pinning output that is not valid Scala:
    // `_` is not a stable identifier. The constructors come into scope through the
    // `import <Enum>.*` that `extractProgram` emits, so the bare name is right.
    assert(result.contains("case Zero"), s"expected 'case Zero', got:\n$result")
    assert(result.contains("case Succ"), s"expected 'case Succ', got:\n$result")
    assert(!result.contains("case _."), s"`_.` is not a valid pattern prefix:\n$result")
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

  test("extractProgram emits IORuntime when IO default shape is present") {
    val ioDef = IndDef(
      name = "IO",
      params = Nil,
      ctors = List(
        CtorDef("pure", List(Term.Ind("Int", Nil, Nil))),
        CtorDef("read_int", Nil),
        CtorDef("print_int", List(Term.Ind("Int", Nil, Nil))),
        CtorDef("bind", List(Term.Ind("IO", Nil, Nil), Term.Pi("_", Term.Ind("Int", Nil, Nil), Term.Ind("IO", Nil, Nil)))),
      ),
      universe = 0,
    )
    val intDef = IndDef(
      name = "Int",
      params = Nil,
      ctors = List(
        CtorDef("zero", Nil),
        CtorDef("pos", List(natInd)),
        CtorDef("neg", List(natInd)),
      ),
      universe = 0,
    )
    val env = GlobalEnv.empty.addInd(natDef).addInd(intDef).addInd(ioDef)
    val result = Extractor.extractProgram(env)
    assert(result.contains("object IORuntime"), s"expected generated runtime, got:\n$result")
    assert(result.contains("def run(script: IO): Int"), s"runtime entrypoint missing, got:\n$result")
    assert(result.contains("def runWithTrace(script: IO, inputs: List[Int]): Trace"), s"trace entrypoint missing, got:\n$result")
    assert(result.contains("final case class Trace("), s"trace payload type missing, got:\n$result")
  }

  test("extractProgram does not emit IORuntime when IO is absent") {
    val env = GlobalEnv.withNat
    val result = Extractor.extractProgram(env)
    assert(!result.contains("object IORuntime"), s"runtime should not be generated, got:\n$result")
  }

  test("termToScalaExpr: Meta becomes ???") {
    val result = Extractor.termToScalaExpr(Term.Meta(42))
    assertEquals(result, "???")
  }

  // ---- builtin Int → scala.Int mapping ----

  val intDef: IndDef = IndDef(
    name     = "Int",
    params   = Nil,
    ctors    = List(
      CtorDef("zero", Nil),
      CtorDef("pos", List(natInd)),
      CtorDef("neg", List(natInd)),
    ),
    universe = 0,
  )

  test("Int builtin: extractInductive produces comment, not enum") {
    val result = Extractor.extractInductive(intDef)
    assert(!result.contains("enum Int:"), s"Int should not produce enum:\n$result")
    assert(result.contains("Int"),        s"should mention Int:\n$result")
  }

  test("Int builtin: termToScalaType(Int) → Int") {
    assertEquals(Extractor.termToScalaType(Term.Ind("Int", Nil, Nil)), "Int")
  }

  test("Int builtin: Con zero → 0") {
    assertEquals(Extractor.termToScalaExpr(Term.Con("zero", "Int", Nil), Nil), "0")
  }

  test("Int builtin: Con pos(n) → n + 1") {
    assertEquals(
      Extractor.termToScalaExpr(Term.Con("pos", "Int", List(Term.Var(0))), List("n")),
      "n + 1",
    )
  }

  test("Int builtin: Con neg(n) → -(n + 1)") {
    assertEquals(
      Extractor.termToScalaExpr(Term.Con("neg", "Int", List(Term.Var(0))), List("n")),
      "-(n + 1)",
    )
  }

  test("Int builtin: match produces if/else chain") {
    // match a { Int.zero => 0  |  Int.pos(n) => n+1  |  Int.neg(n) => -(n+1) }
    val cases = List(
      sroof.core.MatchCase("zero", 0, Term.Var(1)),           // body: 'a' (Var(1) with a in ctx)
      sroof.core.MatchCase("pos",  1, Term.Var(0)),           // body: bound 'n'
      sroof.core.MatchCase("neg",  1, Term.Var(0)),
    )
    val mat    = Term.Mat(Term.Var(0), cases, Term.Ind("Int", Nil, Nil))
    val result = Extractor.termToScalaExpr(mat, List("a"))
    assert(result.contains("if"),   s"should contain 'if':\n$result")
    assert(result.contains("else"), s"should contain 'else':\n$result")
    assert(!result.contains("match"), s"should NOT contain 'match':\n$result")
  }

  // ---- Vec (indexed inductive type) ----

  /** Vec(A: Type)(n: Nat): Type
   *  case nil: Vec(A, zero)
   *  case cons(m: Nat, head: A, tail: Vec[A]): Vec(A, succ(m))
   *
   *  Expected Scala 3 extraction:
   *  enum Vec[A]:
   *    case Nil
   *    case Cons(arg0: A, arg1: Vec[A])
   */
  val vecInd: Term = Term.Ind("Vec", Nil, Nil)  // simplified Vec type reference

  // Inside `argTpes(j)` the scope is the constructor's own earlier arguments first,
  // then `(params ++ indices).reverse` — the layout `Elaborator.elabInductive` builds.
  // So in `cons`, whose args are (m, head, tail):
  //   head's type   (j = 1): Var(0) = m,       Var(1) = n, Var(2) = A
  //   tail's type   (j = 2): Var(0) = head,    Var(1) = m, Var(2) = n, Var(3) = A
  // This fixture used to omit the constructor's own arguments, which agreed with an
  // extractor that also omitted them; both were wrong, and `stdlib/Vec.sroof` shows
  // the real shape.
  val vecDef: IndDef = IndDef(
    name     = "Vec",
    params   = List(Param("A", Term.Uni(0))),        // A: Type  → Scala type param [A]
    ctors    = List(
      CtorDef("nil", Nil),                           // nil: Vec(A, zero) — no args
      CtorDef("cons", List(
        natInd,                                      // m: Nat — the length, ordinary data
        Term.Var(2),                                 // head: A
        Term.App(vecInd, Term.Var(3)),               // tail: Vec[A]
      )),
    ),
    universe = 0,
    indices  = List(Param("n", natInd)),             // n: Nat — index param
  )

  test("extract Vec enum produces a covariant type-parameterized header") {
    // Covariant, because `case Nil` in an invariant generic enum has no way to fix
    // its type argument and dotc rejects the declaration outright.
    val result = Extractor.extractInductive(vecDef)
    assert(result.contains("enum Vec[+A]:"), s"expected 'enum Vec[+A]:', got:\n$result")
  }

  test("extract Vec nil produces case Nil with no args") {
    val result = Extractor.extractInductive(vecDef)
    assert(result.contains("case Nil"), s"expected 'case Nil', got:\n$result")
  }

  test("extract Vec cons keeps the length as data and resolves the type parameter") {
    // The length argument is *not* erased. It looks erasable, because the `enum`
    // header drops the index parameter, but the value a `Cons` stores is what gets
    // passed to every function that takes the length as an argument; dropping it
    // left those calls with nothing to pass (`Not found: _erased0`).
    val result = Extractor.extractInductive(vecDef)
    assert(result.contains("case Cons(arg0: Nat, arg1: A, arg2: Vec[A])"),
      s"expected the full data shape, got:\n$result")
  }

  test("termToScalaType resolves Var against param names") {
    // Var(0) with paramNames=["A"] should resolve to "A"
    assertEquals(Extractor.termToScalaType(Term.Var(0), List("A")), "A")
  }

  test("termToScalaType App with param name resolves type args") {
    // App(Vec, Var(0)) with paramNames=["A"] → "Vec[A]"
    val t = Term.App(vecInd, Term.Var(0))
    assertEquals(Extractor.termToScalaType(t, List("A")), "Vec[A]")
  }
