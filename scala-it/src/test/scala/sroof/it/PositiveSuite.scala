package sroof.it

import munit.FunSuite

/** The vertical slice, compiled for real: ordinary Scala 3 in, verified
 *  theorems out.
 */
class PositiveSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  test("the four Nat theorems compile with the plugin enabled") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def plusZeroLeft(m: Nat): Proof =
        |    prove(plus(Zero, m) === m)(trivial)
        |
        |  @theorem
        |  def plusSuccLeft(n: Nat, m: Nat): Proof =
        |    prove(plus(Succ(n), m) === Succ(plus(n, m)))(trivial)
        |
        |  @theorem
        |  def refl(n: Nat): Proof =
        |    prove(n === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => trivial
        |      })
        |
        |  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a helper definition may call another definition declared later") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  def double(n: Nat): Nat = plus(n, n)
        |
        |  @theorem
        |  def doubleZero: Proof =
        |    prove(double(Zero) === Zero)(trivial)
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("an immutable local val is supported in verified code") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  def twice(n: Nat): Nat =
        |    val once: Nat = plus(n, Zero)
        |    plus(once, Zero)
        |
        |  @theorem
        |  def twiceZero: Proof =
        |    prove(twice(Zero) === Zero)(trivial)
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a wildcard constructor field is accepted") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  def isZero(n: Nat): Nat =
        |    n match
        |      case Zero    => Zero
        |      case Succ(_) => Succ(Zero)
        |
        |  @theorem
        |  def isZeroZero: Proof =
        |    prove(isZero(Zero) === Zero)(trivial)
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a verified theorem can be cited as a simplify lemma by a later theorem") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |
        |  @theorem
        |  def alsoPlusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(simplify(plusZeroRight(n)))
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }
