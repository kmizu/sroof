package sroof.it

import munit.FunSuite

/** Constructs the documentation claims are supported, pinned by an actual
 *  compilation.
 *
 *  Several of these were only ever supported "by reading the extractor". A claim
 *  in a subset table that nothing exercises is a claim that can quietly stop
 *  being true, which for a verification tool is worse than an honest omission.
 */
class SyntaxSurfaceSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private def accepts(body: String): Unit =
    val result = CompilerHarness.compileModule(body)
    assert(result.succeeded, result.report)

  test("a local val with an inferred type is supported") {
    accepts(Fixtures.module(
      """  def twice(n: Nat): Nat =
        |    val once = plus(n, Zero)
        |    plus(once, Zero)
        |
        |  @theorem
        |  def twiceZero: Proof = prove(twice(Zero) === Zero)(trivial)
        |""".stripMargin))
  }

  test("`new Ctor(...)` builds an enum value") {
    accepts(Fixtures.module(
      """  def bump(n: Nat): Nat = new Succ(n)
        |
        |  @theorem
        |  def bumpZero: Proof = prove(bump(Zero) === Succ(Zero))(trivial)
        |""".stripMargin))
  }

  test("enum cases written with an explicit `extends` are supported") {
    accepts(
      """@proofModule
        |object M:
        |  enum Colour:
        |    case Red extends Colour
        |    case Wrapped(inner: Colour) extends Colour
        |
        |  import Colour.*
        |
        |  def peel(c: Colour): Colour =
        |    c match
        |      case Red          => Red
        |      case Wrapped(inn) => peel(inn)
        |
        |  @theorem
        |  def peelRed: Proof = prove(peel(Red) === Red)(trivial)
        |""".stripMargin)
  }

  test("a match on the result of a call is supported") {
    accepts(Fixtures.module(
      """  def pred(n: Nat): Nat =
        |    n match
        |      case Zero    => Zero
        |      case Succ(k) => k
        |
        |  def predOfPlus(n: Nat, m: Nat): Nat =
        |    plus(n, m) match
        |      case Zero    => Zero
        |      case Succ(k) => k
        |
        |  @theorem
        |  def predOfPlusZero: Proof = prove(predOfPlus(Zero, Zero) === Zero)(trivial)
        |""".stripMargin))
  }

  test("a constructor with several non-recursive fields is supported") {
    accepts(
      """@proofModule
        |object M:
        |  enum Flag:
        |    case On
        |    case Off
        |
        |  enum Both:
        |    case Pair(left: Flag, right: Flag)
        |
        |  import Flag.*, Both.*
        |
        |  def swap(b: Both): Both =
        |    b match
        |      case Pair(l, r) => Pair(r, l)
        |
        |  @theorem
        |  def swapTwice: Proof =
        |    prove(swap(swap(Pair(On, Off))) === Pair(On, Off))(trivial)
        |""".stripMargin)
  }

  test("every field may be a wildcard") {
    accepts(
      """@proofModule
        |object M:
        |  enum Flag:
        |    case On
        |    case Off
        |
        |  enum Both:
        |    case Pair(left: Flag, right: Flag)
        |
        |  import Flag.*, Both.*
        |
        |  def constOn(b: Both): Flag =
        |    b match
        |      case Pair(_, _) => On
        |
        |  @theorem
        |  def constOnAlways: Proof = prove(constOn(Pair(On, Off)) === On)(trivial)
        |""".stripMargin)
  }

  test("two enums may refer to each other's types") {
    accepts(
      """@proofModule
        |object M:
        |  enum Tag:
        |    case A
        |    case B
        |
        |  enum Boxed:
        |    case Empty
        |    case Box(tag: Tag, rest: Boxed)
        |
        |  import Tag.*, Boxed.*
        |
        |  def retag(b: Boxed): Boxed =
        |    b match
        |      case Empty       => Empty
        |      case Box(_, rst) => Box(A, retag(rst))
        |
        |  @theorem
        |  def retagIdempotent(b: Boxed): Proof =
        |    prove(retag(retag(b)) === retag(b))(
        |      induction(b) {
        |        case Empty       => trivial
        |        case Box(_, rst) => simplify(ih(rst))
        |      })
        |""".stripMargin)
  }

  test("a nullary definition is supported") {
    accepts(Fixtures.module(
      """  def two: Nat = Succ(Succ(Zero))
        |
        |  @theorem
        |  def twoPlusZero: Proof = prove(plus(two, Zero) === two)(trivial)
        |""".stripMargin))
  }
