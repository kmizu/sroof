package sroof.it

import munit.FunSuite

/** `inductionGeneralizing`, which quantifies the induction hypothesis over other
 *  theorem parameters.
 *
 *  The point of the combinator is goals whose other parameters change as the
 *  recursion proceeds: a hypothesis fixed at the original values simply does not
 *  apply. The first test pins that it works; the second pins that it is not
 *  merely decoration by showing the same proof failing without it.
 */
class GeneralizedInductionSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  /** A function that discards its accumulator, recursing with a changed one.
   *
   *  In the `Succ` branch the goal becomes a statement about `Succ(acc)`, so a
   *  hypothesis fixed at the original `acc` does not apply — and the goal is
   *  stuck, since `n` is a variable rather than a constructor. That makes this
   *  goal unprovable both by `trivial` and by plain induction, which is what
   *  makes it an honest test of the quantified hypothesis.
   */
  private val accumulator =
    """  def alwaysZero(n: Nat, acc: Nat): Nat =
      |    n match
      |      case Zero    => Zero
      |      case Succ(k) => alwaysZero(k, Succ(acc))
      |
      |  @theorem
      |  def alwaysZeroIsZero(n: Nat, acc: Nat): Proof =
      |    prove(alwaysZero(n, acc) === Zero)(
      |      %TACTIC%)
      |""".stripMargin

  test("the goal is not provable by trivial alone") {
    // Guards against the positive test below becoming vacuous: if the statement
    // held definitionally, it would pass no matter what the hypothesis did.
    val result = CompilerHarness.compileModule(Fixtures.module(
      accumulator.replace("%TACTIC%", "trivial")))
    assert(result.failed, s"the goal held definitionally:\n${result.report}")
  }

  test("inductionGeneralizing plus exactIh proves an accumulator goal") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      accumulator.replace("%TACTIC%",
        """inductionGeneralizing(n, acc) {
          |        case Zero    => trivial
          |        case Succ(k) => exactIh(k)(Succ(acc))
          |      }""".stripMargin)))
    assert(result.succeeded, result.report)
  }

  test("the same goal is not provable by plain induction") {
    // Pins that the combinator earns its place: with the hypothesis fixed at the
    // original `acc`, this proof does not go through.
    val result = CompilerHarness.compileModule(Fixtures.module(
      accumulator.replace("%TACTIC%",
        """induction(n) {
          |        case Zero    => trivial
          |        case Succ(k) => simplify(ih(k))
          |      }""".stripMargin)))
    assert(result.failed, s"plain induction unexpectedly proved this:\n${result.report}")
    assert(result.hasSroofError, result.report)
  }

  test("exactIh outside an induction branch is rejected") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def bad(n: Nat): Proof = prove(n === n)(exactIh(n)(n))
        |""".stripMargin))
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("only available inside an induction branch"), result.report)
  }

  test("generalizing over a non-parameter is rejected") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def bad(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      inductionGeneralizing(n, Zero) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin))
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("only another parameter of this"), result.report)
  }

  test("inductionGeneralizing with no parameters to generalize is rejected") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def bad(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      inductionGeneralizing(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin))
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("at least one parameter"), result.report)
  }

  test("a false goal is not rescued by generalizing") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def bogus(n: Nat, m: Nat): Proof =
        |    prove(plus(n, Succ(m)) === plus(n, m))(
        |      inductionGeneralizing(n, m) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin))
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("theorem bogus"), result.report)
  }
