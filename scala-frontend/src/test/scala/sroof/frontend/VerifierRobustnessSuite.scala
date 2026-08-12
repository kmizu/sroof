package sroof.frontend

import munit.FunSuite

/** `ModuleVerifier.verify` says errors are "returned, never thrown". They were not.
  *
  * `Eval` throws on a term it cannot reduce — an unbound index, a match with no
  * branch for the scrutinee's constructor — and every such term reaching this
  * layer comes from an ill-typed core term, which is exactly what a bridge bug
  * produces. On the `.sroof` path every entry to evaluation is wrapped
  * (`Checker.executeProof`, `Bidirectional.whnf`, `Kernel.check`) so the exception
  * becomes a rejection. On this path nothing was, so it left `verify` and reached
  * dotc as a crash with no source position, instead of an error on the theorem
  * that caused it.
  *
  * The claim of a `have` is the repro used here because it is translated and
  * evaluated inside the tactic engine, which is upstream of the kernel's own
  * handlers and outside the theorem statement that `wellFormedProp` checks.
  */
class VerifierRobustnessSuite extends FunSuite:

  private val sp = SourceSpan.synthetic
  private def sym(s: String) = SymbolId(s)

  private val boolId = sym("M.Bool")
  private val trueId = sym("M.Bool.True")
  private val boolInd = ResolvedInductive(
    boolId, "Bool",
    List(ResolvedConstructor(trueId, "True", Nil, sp),
         ResolvedConstructor(sym("M.Bool.False"), "False", Nil, sp)),
    sp)

  private val tru: ResolvedExpr = ResolvedExpr.Construct(boolId, trueId, "True", Nil, sp)

  /** `plus(Bool.True, Nat.Zero)`: `plus` matches on a `Nat`, so evaluating this
    * finds no branch for `True` and throws.
    */
  private val illTyped: ResolvedExpr =
    ResolvedExpr.Call(NatFixture.plusId, "plus", List(tru, NatFixture.zero), sp)

  test("an unreducible term is a rejection, not an exception"):
    val tactic = ResolvedTactic.Have(
      illTyped, illTyped, "h",
      ResolvedTactic.Trivial(sp),
      ResolvedTactic.Trivial(sp),
      sp)
    val theorem = ResolvedTheorem(
      sym("M.t"), "t", Nil,
      ResolvedProp(NatFixture.natTpe, NatFixture.zero, NatFixture.zero, sp),
      tactic, isSimp = false, sp)
    val module = ResolvedModule(
      sym("M"), "M", List(NatFixture.natInd, boolInd),
      List(NatFixture.plusDef), List(theorem), sp)

    // The assertion is the *shape* of the answer: any `Left` is fine, a throw is
    // not. Before the fix this line raised `RuntimeException: Non-exhaustive
    // match: no case for constructor 'True'`.
    ModuleVerifier.verify(module) match
      case Left(err) => assert(err.message.nonEmpty, "a rejection with no message")
      case Right(_)  => fail("a theorem resting on an unreducible term was accepted")
