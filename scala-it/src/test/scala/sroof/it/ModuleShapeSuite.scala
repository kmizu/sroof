package sroof.it

import munit.FunSuite

/** Shapes a proof module can take, and orderings the frontend claims to
 *  normalise.
 *
 *  Everything here was reachable by reading the extractor but exercised by
 *  nothing. Branch reordering in particular is a silent-failure risk: `Term.Mat`
 *  matches branches to constructors *by position*, so if the normalisation were
 *  wrong the proof would be about the wrong branches rather than fail outright.
 */
class ModuleShapeSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private def accepts(body: String): Unit =
    val result = CompilerHarness.compileModule(body)
    assert(result.succeeded, result.report)

  test("match branches written out of declaration order are normalised") {
    accepts(Fixtures.module(
      """  def pred(n: Nat): Nat =
        |    n match
        |      case Succ(k) => k
        |      case Zero    => Zero
        |
        |  @theorem
        |  def predZero: Proof = prove(pred(Zero) === Zero)(trivial)
        |
        |  @theorem
        |  def predSucc(n: Nat): Proof = prove(pred(Succ(n)) === n)(trivial)
        |""".stripMargin))
  }

  test("induction branches written out of declaration order are normalised") {
    accepts(Fixtures.module(
      """  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Succ(k) => simplify(ih(k))
        |        case Zero    => trivial
        |      })
        |""".stripMargin))
  }

  test("two proof modules in one file are both verified") {
    val result = CompilerHarness.compileModule(
      """@proofModule
        |object A:
        |  enum Nat:
        |    case Zero
        |    case Succ(n: Nat)
        |  import Nat.*
        |  def plus(n: Nat, m: Nat): Nat =
        |    n match
        |      case Zero    => m
        |      case Succ(k) => Succ(plus(k, m))
        |  @theorem
        |  def ok(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |
        |@proofModule
        |object B:
        |  enum Colour:
        |    case Red
        |    case Deep(c: Colour)
        |  import Colour.*
        |  def peel(c: Colour): Colour =
        |    c match
        |      case Red     => Red
        |      case Deep(i) => peel(i)
        |  @theorem
        |  def peelRed: Proof = prove(peel(Red) === Red)(trivial)
        |""".stripMargin)
    assert(result.succeeded, result.report)
  }

  test("a failure in the second module of a file still fails the compilation") {
    val result = CompilerHarness.compileModule(
      """@proofModule
        |object A:
        |  enum Nat:
        |    case Zero
        |    case Succ(n: Nat)
        |  import Nat.*
        |  @theorem
        |  def fine(n: Nat): Proof = prove(n === n)(trivial)
        |
        |@proofModule
        |object B:
        |  enum Colour:
        |    case Red
        |    case Deep(c: Colour)
        |  import Colour.*
        |  @theorem
        |  def broken(c: Colour): Proof = prove(c === Red)(trivial)
        |""".stripMargin)
    assert(result.failed, result.report)
    assert(result.mentions("theorem broken"), result.report)
  }

  test("an enum with more than two cases is supported") {
    accepts(
      """@proofModule
        |object M:
        |  enum Colour:
        |    case Red
        |    case Green
        |    case Blue
        |    case Shade(base: Colour)
        |
        |  import Colour.*
        |
        |  def normalise(c: Colour): Colour =
        |    c match
        |      case Red      => Red
        |      case Green    => Green
        |      case Blue     => Blue
        |      case Shade(b) => normalise(b)
        |
        |  @theorem
        |  def normaliseIdempotent(c: Colour): Proof =
        |    prove(normalise(normalise(c)) === normalise(c))(
        |      induction(c) {
        |        case Red      => trivial
        |        case Green    => trivial
        |        case Blue     => trivial
        |        case Shade(b) => simplify(ih(b))
        |      })
        |""".stripMargin)
  }

  test("a chain of definitions is inlined transitively") {
    accepts(Fixtures.module(
      """  def once(n: Nat): Nat  = plus(n, Zero)
        |  def twice(n: Nat): Nat = once(once(n))
        |  def thrice(n: Nat): Nat = twice(once(n))
        |
        |  @theorem
        |  def thriceZero: Proof = prove(thrice(Zero) === Zero)(trivial)
        |""".stripMargin))
  }

  test("simplify may cite several verified theorems at once") {
    accepts(Fixtures.module(
      """  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |
        |  @theorem
        |  def plusZeroLeft(n: Nat): Proof = prove(plus(Zero, n) === n)(trivial)
        |
        |  @theorem
        |  def both(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(simplify(plusZeroRight(n), plusZeroLeft(n)))
        |""".stripMargin))
  }

  test("deeply nested constructor expressions are supported") {
    accepts(Fixtures.module(
      """  @theorem
        |  def four: Proof =
        |    prove(plus(Succ(Succ(Zero)), Succ(Succ(Zero))) === Succ(Succ(Succ(Succ(Zero)))))(trivial)
        |""".stripMargin))
  }
