package sroof.it

import munit.FunSuite

/** `have`: prove an intermediate equation, then continue with it in scope.
 *
 *  The intermediate claim is a goal in its own right, so it goes through the
 *  same kernel check as everything else — `have` cannot be used to assume
 *  something convenient.
 */
class HaveSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  test("have proves an intermediate step and uses it") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) =>
        |          have(plus(k, Zero) === k)(simplify(ih(k))) { step =>
        |            simplify(step)
        |          }
        |      })
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("have works at the top level of a proof") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def twoIsTwo: Proof =
        |    prove(plus(Succ(Zero), Succ(Zero)) === Succ(Succ(Zero)))(
        |      have(plus(Zero, Succ(Zero)) === Succ(Zero))(trivial) { step =>
        |        trivial
        |      })
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a have claim that does not hold fails the theorem") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def bogus(n: Nat): Proof =
        |    prove(plus(Zero, n) === n)(
        |      have(plus(n, Zero) === Succ(n))(trivial) { step =>
        |        trivial
        |      })
        |""".stripMargin))
    assert(result.failed, s"an unprovable have claim was accepted:\n${result.report}")
    assert(result.hasSroofError, result.report)
    assert(result.mentions("theorem bogus"), result.report)
  }

  test("a have hypothesis may not be named ih") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def shadow(n: Nat): Proof =
        |    prove(plus(Zero, n) === n)(
        |      have(plus(Zero, n) === n)(trivial) { ih =>
        |        trivial
        |      })
        |""".stripMargin))
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("reserved for the generated induction hypothesis"), result.report)
  }

  test("a have claim must be an equality") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  def id(n: Nat): Nat = n
        |
        |  @theorem
        |  def bad(n: Nat): Proof =
        |    prove(plus(Zero, n) === n)(
        |      have(Impostor.claim(n))(trivial) { step => trivial })
        |""".stripMargin) +
      """
        |object Impostor:
        |  def claim(n: M.Nat): sroof.lang.Prop = sroof.lang.===(n)(n)
        |""".stripMargin)
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("must be an equality built with sroof"), result.report)
  }
