package sroof.frontend

import munit.FunSuite

/** A theorem's statement must be a proposition before a proof of it means anything.
  *
  * `ProofRunner.verifyTheorem` asks the kernel whether the generated term has the
  * claimed type. It never asks whether the claimed type *is* a type. The claim
  * comes from `CoreTranslator.translateProp`, which is inside the trust boundary,
  * so nothing re-checks it.
  *
  * Two things make the gap reachable rather than theoretical. `translateProp`
  * discards the declared type — it builds the **2-argument** `Eq` form, whose type
  * slot is `Meta(-1)` — and `Kernel.check`'s `refl` special case returns success on
  * a `Meta` slot without checking the term has any type at all, on the recorded
  * assumption that "a was already type-checked by the bidirectional checker". For
  * this caller that assumption does not hold.
  *
  * The result is a module that exports a verified theorem whose statement is not a
  * proposition, and which later proofs may then cite as a lemma.
  */
class PropWellFormedSuite extends FunSuite:

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

  /** `plus(Bool.True, Nat.Zero)` — `plus` takes two `Nat`s, so this is not a term
    * of any type. It is reflexively equal to itself, which is exactly why `trivial`
    * closes it and the gap stays invisible.
    */
  private val illTyped: ResolvedExpr =
    ResolvedExpr.Call(NatFixture.plusId, "plus", List(tru, NatFixture.zero), sp)

  private def moduleWith(goal: ResolvedProp, tactic: ResolvedTactic) =
    ResolvedModule(
      sym("M"), "M",
      List(NatFixture.natInd, boolInd),
      List(NatFixture.plusDef),
      List(ResolvedTheorem(sym("M.t"), "t", Nil, goal, tactic, isSimp = false, sp)),
      sp)

  test("a theorem whose statement is not a proposition is rejected"):
    val goal = ResolvedProp(NatFixture.natTpe, illTyped, illTyped, sp)
    ModuleVerifier.verify(moduleWith(goal, ResolvedTactic.Trivial(sp))) match
      case Right(m) =>
        fail("the verifier reported a proved theorem whose statement is ill-typed: " +
             m.theorems.map(_.entry.tpe.show).mkString(", "))
      case Left(err) =>
        assert(err.message.contains("statement is not a proposition"),
          s"rejected, but not as a malformed statement: ${err.message}")

  test("a well-formed statement is still proved"):
    // The control: the same shape with `plus` applied to what it actually takes.
    val ok = ResolvedExpr.Call(NatFixture.plusId, "plus",
      List(NatFixture.zero, NatFixture.zero), sp)
    val goal = ResolvedProp(NatFixture.natTpe, ok, NatFixture.zero, sp)
    ModuleVerifier.verify(moduleWith(goal, ResolvedTactic.Trivial(sp))) match
      case Right(m)  => assertEquals(m.theorems.map(_.name), List("t"))
      case Left(err) => fail(s"a well-formed theorem was rejected: ${err.message}")
