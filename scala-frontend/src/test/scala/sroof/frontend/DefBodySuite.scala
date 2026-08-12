package sroof.frontend

import munit.FunSuite

/** A definition must mean what it says it means.
  *
  * `CoreTranslator.translateDef` checks termination and then trusts itself. It is
  * *inside* the trust boundary — it is the component that decides what core term a
  * Scala definition is about — so when it produced an ill-typed body there was no
  * one left to notice. The Scala typer does not help: it checks the Scala program,
  * and the open question is whether the core term still says the same thing.
  *
  * The `.sroof` frontend closed this in v0.14 (`Checker.checkDefBodies`). The
  * Scala frontend, added later, never grew the equivalent, so the same defect was
  * live on the newer of the two paths.
  *
  * The IR built here is what a `TreeExtractor` bug looks like from the verifier's
  * side: a resolved definition whose declared result type and whose body disagree.
  * Every case below is accepted by the translator — that is the point — so before
  * the fix `verify` returned `Right` on all of them.
  */
class DefBodySuite extends FunSuite:

  private val sp = SourceSpan.synthetic
  private def sym(s: String) = SymbolId(s)

  private val boolId  = sym("M.Bool")
  private val trueId  = sym("M.Bool.True")
  private val falseId = sym("M.Bool.False")
  private val boolTpe: ResolvedType = ResolvedType.Inductive(boolId, "Bool")
  private val boolInd = ResolvedInductive(
    boolId, "Bool",
    List(ResolvedConstructor(trueId, "True", Nil, sp),
         ResolvedConstructor(falseId, "False", Nil, sp)),
    sp)

  private val natTpe = NatFixture.natTpe
  private val tru: ResolvedExpr = ResolvedExpr.Construct(boolId, trueId, "True", Nil, sp)

  private def moduleOf(d: ResolvedDef) =
    ResolvedModule(sym("M"), "M", List(NatFixture.natInd, boolInd), List(d), Nil, sp)

  private def verify(d: ResolvedDef) = ModuleVerifier.verify(moduleOf(d))

  /** `n` bound as a `Nat` parameter, so every case below is a well-formed def
    * apart from the type its body actually has.
    */
  private val n = ResolvedBinder(sym("f.n"), "n", natTpe)
  private val nRef = ResolvedExpr.Local(sym("f.n"), "n", sp)

  private def defWith(result: ResolvedType, body: ResolvedExpr) =
    ResolvedDef(sym("M.f"), "f", List(n), result, body, sp)

  private def assertRejected(d: ResolvedDef, label: String): Unit =
    verify(d) match
      case Right(_) =>
        fail(s"$label: the verifier accepted a definition whose body is not of its declared type")
      case Left(err) =>
        // A rejection for the wrong reason would be just as blind, so the message
        // has to be the kernel's, not the translator's arity or scoping check.
        assert(err.message.contains("does not match its declared type"),
          s"$label: rejected, but not by the kernel: ${err.message}")

  test("a body of the wrong type is rejected"):
    // `def f(n: Nat): Nat = Bool.True`
    assertRejected(defWith(natTpe, tru), "whole body")

  test("a single match branch of the wrong type is rejected"):
    // The subtle one. The expected type is threaded top-down and used *verbatim*
    // as the `Mat` return type, so a branch that does not have that type is
    // written into a term claiming it does. One branch is deliberately correct:
    // a check that only looked at the first branch would pass this.
    val body = ResolvedExpr.Match(
      nRef,
      List(
        ResolvedCase(NatFixture.zeroId, "Zero", Nil, NatFixture.zero, sp),
        ResolvedCase(NatFixture.succId, "Succ",
          List(ResolvedBinder(sym("f.k"), "k", natTpe)), tru, sp),
      ),
      sp, natTpe)
    assertRejected(defWith(natTpe, body), "match branch")

  test("a let-bound value of the wrong type is rejected"):
    // `def f(n: Nat): Nat = { val b: Nat = Bool.True; b }` — the binder claims a
    // type its value does not have, which the `let` translation records verbatim.
    val b = ResolvedBinder(sym("f.b"), "b", natTpe)
    val body = ResolvedExpr.Let(b, tru, ResolvedExpr.Local(sym("f.b"), "b", sp), sp)
    assertRejected(defWith(natTpe, body), "let binding")

  test("a well-typed definition is still accepted"):
    // The control. Without it, a fix that rejected everything would pass the three
    // cases above and look like progress.
    val body = ResolvedExpr.Match(
      nRef,
      List(
        ResolvedCase(NatFixture.zeroId, "Zero", Nil, NatFixture.zero, sp),
        ResolvedCase(NatFixture.succId, "Succ",
          List(ResolvedBinder(sym("f.k"), "k", natTpe)),
          ResolvedExpr.Local(sym("f.k"), "k", sp), sp),
      ),
      sp, natTpe)
    verify(defWith(natTpe, body)) match
      case Right(_)  => ()
      case Left(err) => fail(s"a well-typed definition was rejected: ${err.message}")
