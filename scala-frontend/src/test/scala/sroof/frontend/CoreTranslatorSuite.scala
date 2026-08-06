package sroof.frontend

import munit.FunSuite
import sroof.core.{CtorDef, GlobalEnv, MatchCase, Term}

/** Golden tests for the Scala-to-core bridge.
 *
 *  These pin the exact core shape, not just "it translated".  A silent change
 *  in binder order would still type-check but would mean the theorems are about
 *  a different function than the one the user wrote — the one class of bug the
 *  kernel cannot catch for us.
 */
class CoreTranslatorSuite extends FunSuite:

  private val nat  = Term.Ind("Nat", Nil, Nil)
  private val tenv = CoreTranslator.TranslationEnv(NatFixture.module)

  test("enum Nat translates to IndDef with constructors in declaration order") {
    val ind = CoreTranslator.translateInductive(NatFixture.natInd).fold(e => fail(e.render), identity)
    assertEquals(ind.name, "Nat")
    assertEquals(ind.params, Nil)
    assertEquals(ind.universe, 0)
    assertEquals(ind.ctors, List(CtorDef("Zero", Nil), CtorDef("Succ", List(nat))))
  }

  test("plus translates to the exact expected core term") {
    val entry = CoreTranslator.translateDef(NatFixture.plusDef, tenv)
      .fold(e => fail(e.render), identity)

    val expectedTpe = Term.Pi("n", nat, Term.Pi("m", nat, nat))
    assertEquals(entry.tpe, expectedTpe)

    // Inside Lam(n, Lam(m, ...)):  m = Var(0), n = Var(1), plus (Fix binder) = Var(2).
    // Inside the Succ branch one more binder (k) is in scope, so everything
    // shifts by one: k = Var(0), m = Var(1), n = Var(2), plus = Var(3).
    val expectedBody = Term.Fix("plus", expectedTpe,
      Term.Lam("n", nat,
        Term.Lam("m", nat,
          Term.Mat(
            Term.Var(1),
            List(
              MatchCase("Zero", 0, Term.Var(0)),
              MatchCase("Succ", 1,
                Term.Con("Succ", "Nat",
                  List(Term.App(Term.App(Term.Var(3), Term.Var(0)), Term.Var(1))))),
            ),
            nat))))
    assertEquals(entry.body, expectedBody)
  }

  test("no unresolved metavariable survives an accepted translation") {
    val entry = CoreTranslator.translateDef(NatFixture.plusDef, tenv)
      .fold(e => fail(e.render), identity)
    assert(!containsMeta(entry.body), "translated body contains a Meta node")
    assert(!containsMeta(entry.tpe), "translated type contains a Meta node")
  }

  test("the translated plus type-checks against its own declared type") {
    val ind = CoreTranslator.translateInductive(NatFixture.natInd).fold(e => fail(e.render), identity)
    given GlobalEnv = GlobalEnv.empty.addInd(ind)
    val entry = CoreTranslator.translateDef(NatFixture.plusDef, tenv)
      .fold(e => fail(e.render), identity)
    sroof.checker.Bidirectional.check(sroof.core.Context.empty, entry.body, entry.tpe) match
      case Left(err) => fail(s"translated plus did not type-check: ${err.getMessage}")
      case Right(_)  => ()
  }

  test("core plus agrees with Scala plus on small values (differential check)") {
    val ind = CoreTranslator.translateInductive(NatFixture.natInd).fold(e => fail(e.render), identity)
    given GlobalEnv = GlobalEnv.empty.addInd(ind)
    val entry = CoreTranslator.translateDef(NatFixture.plusDef, tenv)
      .fold(e => fail(e.render), identity)

    def encode(n: Int): Term =
      if n == 0 then Term.Con("Zero", "Nat", Nil)
      else Term.Con("Succ", "Nat", List(encode(n - 1)))

    def decode(t: Term): Int = t match
      case Term.Con("Zero", "Nat", Nil)      => 0
      case Term.Con("Succ", "Nat", List(a))  => 1 + decode(a)
      case other                             => fail(s"not a Nat literal: ${other.show}")

    val env = sroof.eval.EnvBuilder.fromContext(sroof.core.Context.empty)
    for
      a <- 0 to 3
      b <- 0 to 3
    do
      val applied = Term.App(Term.App(entry.body, encode(a)), encode(b))
      val result  = decode(sroof.eval.Quote.normalize(0, env, applied))
      assertEquals(result, a + b, s"core plus($a, $b) disagreed with Scala")
  }

  test("mutual recursion is rejected with both participants named") {
    val a = NatFixture.sym("M.a")
    val b = NatFixture.sym("M.b")
    val sp = SourceSpan.synthetic
    val x  = ResolvedBinder(NatFixture.sym("x"), "x", NatFixture.natTpe)
    def callTo(id: SymbolId, name: String) =
      ResolvedDef(id, name, List(x), NatFixture.natTpe,
        ResolvedExpr.Call(if id == a then b else a, if id == a then "b" else "a",
          List(ResolvedExpr.Local(NatFixture.sym("x"), "x", sp)), sp), sp)
    val module = NatFixture.module.copy(definitions = List(callTo(a, "a"), callTo(b, "b")))
    CoreTranslator.orderDefinitions(module) match
      case Right(_)  => fail("mutual recursion was accepted")
      case Left(err) =>
        assert(err.message.contains("mutual recursion"), err.message)
        assert(err.message.contains("cycle among: a, b"), err.message)
  }

  test("a non-exhaustive match is rejected") {
    val partial = NatFixture.plusDef.copy(
      body = ResolvedExpr.Match(
        NatFixture.local("plus.n", "n"),
        List(ResolvedCase(NatFixture.zeroId, "Zero", Nil,
          NatFixture.local("plus.m", "m"), SourceSpan.synthetic)),
        SourceSpan.synthetic, NatFixture.natTpe))
    CoreTranslator.translateDef(partial, tenv) match
      case Right(_)  => fail("non-exhaustive match was accepted")
      case Left(err) => assert(err.message.contains("missing branch"), err.message)
  }

  private def containsMeta(t: Term): Boolean = t match
    case Term.Meta(_)            => true
    case Term.App(f, a)          => containsMeta(f) || containsMeta(a)
    case Term.Lam(_, tp, b)      => containsMeta(tp) || containsMeta(b)
    case Term.Pi(_, d, c)        => containsMeta(d) || containsMeta(c)
    case Term.Let(_, tp, df, b)  => containsMeta(tp) || containsMeta(df) || containsMeta(b)
    case Term.Con(_, _, args)    => args.exists(containsMeta)
    case Term.Fix(_, tp, b)      => containsMeta(tp) || containsMeta(b)
    case Term.Mat(s, cs, rt)     => containsMeta(s) || containsMeta(rt) || cs.exists(c => containsMeta(c.body))
    case Term.Ind(_, ps, cs)     => ps.exists(p => containsMeta(p.tpe)) || cs.exists(c => containsMeta(c.tpe))
    case Term.Var(_) | Term.Uni(_) => false
