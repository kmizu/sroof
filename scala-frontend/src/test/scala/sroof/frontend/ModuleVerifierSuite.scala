package sroof.frontend

import munit.FunSuite

/** End-to-end frontend tests: IR in, kernel-accepted theorems out.
 *
 *  No compiler is involved here, so a failure points at the translation or the
 *  proof runner rather than at tree extraction.
 */
class ModuleVerifierSuite extends FunSuite:

  private val sp = SourceSpan.synthetic

  test("all four Nat theorems are proved and accepted by the kernel") {
    val verified = ModuleVerifier.verify(NatFixture.module).fold(e => fail(e.render), identity)
    assertEquals(
      verified.theorems.map(_.name),
      List("plusZeroLeft", "plusSuccLeft", "refl", "plusZeroRight"))
    assert(verified.env.lookupInd("Nat").isDefined)
    assert(verified.env.lookupDef("plus").isDefined)
  }

  test("a false theorem attempted with trivial is rejected") {
    // plus(n, Zero) === Succ(n) is false; trivial cannot close it.
    val n = ResolvedBinder(NatFixture.sym("th.n"), "n", NatFixture.natTpe)
    val bogus = ResolvedTheorem(
      NatFixture.sym("NatProofs.bogus"), "bogus", List(n),
      ResolvedProp(NatFixture.natTpe,
        NatFixture.plus(NatFixture.local("th.n", "n"), NatFixture.zero),
        NatFixture.succ(NatFixture.local("th.n", "n")), sp),
      ResolvedTactic.Trivial(sp), isSimp = false, sp)
    ModuleVerifier.verify(NatFixture.module.copy(theorems = List(bogus))) match
      case Right(_)  => fail("a false theorem was accepted")
      case Left(err) => assertEquals(err.subject, "theorem bogus")
  }

  test("a false inductive theorem is rejected") {
    // plus(n, Zero) === Succ(n) attempted by induction: the base case fails.
    val n = ResolvedBinder(NatFixture.sym("th.n"), "n", NatFixture.natTpe)
    val k = ResolvedBinder(NatFixture.sym("th.k"), "k", NatFixture.natTpe)
    val bogus = ResolvedTheorem(
      NatFixture.sym("NatProofs.bogusInd"), "bogusInd", List(n),
      ResolvedProp(NatFixture.natTpe,
        NatFixture.plus(NatFixture.local("th.n", "n"), NatFixture.zero),
        NatFixture.succ(NatFixture.local("th.n", "n")), sp),
      ResolvedTactic.Induction(NatFixture.sym("th.n"), "n", List(
        ResolvedTacticCase(NatFixture.zeroId, "Zero", Nil, usesIh = false,
          ResolvedTactic.Trivial(sp), sp),
        ResolvedTacticCase(NatFixture.succId, "Succ", List(k), usesIh = true,
          ResolvedTactic.Simplify(
            List(ResolvedLemmaRef.InductionHypothesis(NatFixture.sym("th.k"), "k", sp)), sp), sp),
      ), sp), isSimp = false, sp)
    ModuleVerifier.verify(NatFixture.module.copy(theorems = List(bogus))) match
      case Right(_)  => fail("a false inductive theorem was accepted")
      case Left(err) => assertEquals(err.subject, "theorem bogusInd")
  }

  test("a simplify lemma naming an unverified theorem is rejected") {
    val n = ResolvedBinder(NatFixture.sym("th.n"), "n", NatFixture.natTpe)
    val bogus = ResolvedTheorem(
      NatFixture.sym("NatProofs.usesGhost"), "usesGhost", List(n),
      ResolvedProp(NatFixture.natTpe,
        NatFixture.local("th.n", "n"), NatFixture.local("th.n", "n"), sp),
      ResolvedTactic.Simplify(
        List(ResolvedLemmaRef.Theorem(NatFixture.sym("ghost"), "ghost", sp)), sp),
      isSimp = false, sp)
    ModuleVerifier.verify(NatFixture.module.copy(theorems = List(bogus))) match
      case Right(_)  => fail("a proof citing an unverified lemma was accepted")
      case Left(err) => assert(err.message.contains("already been verified"), err.message)
  }

  test("cases proves a goal that needs only a constructor split") {
    val n = ResolvedBinder(NatFixture.sym("th.n"), "n", NatFixture.natTpe)
    val k = ResolvedBinder(NatFixture.sym("th.k"), "k", NatFixture.natTpe)
    val thm = ResolvedTheorem(
      NatFixture.sym("NatProofs.viaCases"), "viaCases", List(n),
      ResolvedProp(NatFixture.natTpe,
        NatFixture.plus(NatFixture.zero, NatFixture.local("th.n", "n")),
        NatFixture.local("th.n", "n"), sp),
      ResolvedTactic.Cases(NatFixture.sym("th.n"), "n", List(
        ResolvedTacticCase(NatFixture.zeroId, "Zero", Nil, usesIh = false,
          ResolvedTactic.Trivial(sp), sp),
        ResolvedTacticCase(NatFixture.succId, "Succ", List(k), usesIh = false,
          ResolvedTactic.Trivial(sp), sp),
      ), sp), isSimp = false, sp)
    val verified = ModuleVerifier
      .verify(NatFixture.module.copy(theorems = List(thm)))
      .fold(e => fail(e.render), identity)
    assertEquals(verified.theorems.map(_.name), List("viaCases"))
  }

  test("rewrite closes an inductive goal with the hypothesis") {
    val n = ResolvedBinder(NatFixture.sym("th.n"), "n", NatFixture.natTpe)
    val k = ResolvedBinder(NatFixture.sym("th.k"), "k", NatFixture.natTpe)
    val thm = ResolvedTheorem(
      NatFixture.sym("NatProofs.viaRewrite"), "viaRewrite", List(n),
      ResolvedProp(NatFixture.natTpe,
        NatFixture.plus(NatFixture.local("th.n", "n"), NatFixture.zero),
        NatFixture.local("th.n", "n"), sp),
      ResolvedTactic.Induction(NatFixture.sym("th.n"), "n", List(
        ResolvedTacticCase(NatFixture.zeroId, "Zero", Nil, usesIh = false,
          ResolvedTactic.Trivial(sp), sp),
        ResolvedTacticCase(NatFixture.succId, "Succ", List(k), usesIh = true,
          ResolvedTactic.Rewrite(
            List(ResolvedLemmaRef.InductionHypothesis(NatFixture.sym("th.k"), "k", sp)), sp), sp),
      ), sp), isSimp = false, sp)
    val verified = ModuleVerifier
      .verify(NatFixture.module.copy(theorems = List(thm)))
      .fold(e => fail(e.render), identity)
    assertEquals(verified.theorems.map(_.name), List("viaRewrite"))
  }

  test("a @simp theorem enters simpSet only after the kernel accepts it") {
    val simped = NatFixture.plusZeroRight.copy(isSimp = true)
    val verified = ModuleVerifier
      .verify(NatFixture.module.copy(theorems = List(simped)))
      .fold(e => fail(e.render), identity)
    assert(verified.env.simpSet.contains("plusZeroRight"))
  }
