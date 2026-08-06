package sroof.it

import munit.FunSuite

/** Verified *computation* that must be rejected.
 *
 *  Being legal Scala does not make code legal verified sroof code.  The point of
 *  these tests is that unsupported constructs fail closed rather than being
 *  approximated — a mistranslated definition would produce a theorem about a
 *  function the user never wrote, and the kernel could not detect that.
 */
class NegativeCodeSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private def rejects(body: String)(check: CompilerHarness.Result => Unit): Unit =
    val result = CompilerHarness.compileModule(body)
    assert(result.failed, s"expected compilation to fail, but it succeeded:\n$body")
    assert(result.hasSroofError, s"failure did not come from sroof:\n${result.report}")
    check(result)

  test("a mutable field in a proof module is rejected") {
    rejects(Fixtures.module(
      """  var counter: Nat = Zero
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("mutable field (var)"), r.report)
    }
  }

  test("an assignment inside a verified definition is rejected") {
    rejects(Fixtures.module(
      """  def bad(n: Nat): Nat =
        |    var acc: Nat = n
        |    acc = Zero
        |    acc
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("verified definition bad"), r.report)
    }
  }

  test("an external effect in verified computation is rejected") {
    rejects(Fixtures.module(
      """  def loud(n: Nat): Nat =
        |    println("hello")
        |    n
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("verified definition loud"), r.report)
    }
  }

  test("non-structural recursion is rejected") {
    rejects(Fixtures.module(
      """  def spin(n: Nat): Nat = spin(Succ(n))
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("structurally decreasing"), r.report)
    }
  }

  test("mutual recursion is rejected") {
    rejects(Fixtures.module(
      """  def isEven(n: Nat): Nat =
        |    n match
        |      case Zero    => Zero
        |      case Succ(k) => isOdd(k)
        |
        |  def isOdd(n: Nat): Nat =
        |    n match
        |      case Zero    => Succ(Zero)
        |      case Succ(k) => isEven(k)
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("mutual recursion"), r.report)
    }
  }

  test("a call to a method outside the proof module is rejected") {
    rejects(Fixtures.module(
      """  def viaOutside(n: Nat): Nat = Helper.identity(n)
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin) +
      """
        |object Helper:
        |  def identity(n: M.Nat): M.Nat = n
        |""".stripMargin) { r =>
      assert(r.mentions("not verified code"), r.report)
    }
  }

  test("an unsupported parameter type is rejected") {
    rejects(Fixtures.module(
      """  def widen(n: Int): Nat = Zero
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("is not supported"), r.report)
    }
  }

  test("a class declared in a proof module is rejected") {
    rejects(Fixtures.module(
      """  case class Box(n: Nat)
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("which is not an enum"), r.report)
    }
  }

  test("a type parameter used outside its own definition is rejected") {
    // Generic enums are supported as of v0.7; what is still rejected is a type
    // that is neither an enum of this module nor a parameter in scope.
    rejects(Fixtures.bareModule(
      """  enum Box[A]:
        |    case Full(a: A)
        |
        |  def unwrap(b: Box[Int]): Box[Int] = b
        |""".stripMargin)) { r =>
      assert(r.mentions("is not supported"), r.report)
    }
  }

  test("a pattern guard in verified code is rejected") {
    rejects(Fixtures.module(
      """  def guarded(n: Nat): Nat =
        |    n match
        |      case Succ(k) if true => k
        |      case Succ(k)         => k
        |      case Zero            => Zero
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("guards are not supported"), r.report)
    }
  }

  test("a lambda in verified code is rejected") {
    rejects(Fixtures.module(
      """  def higherOrder(n: Nat): Nat =
        |    val f: Nat => Nat = x => x
        |    f(n)
        |
        |  @theorem
        |  def thm(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("verified definition higherOrder"), r.report)
    }
  }
