package sroof.it

import munit.FunSuite

/** Generic enums: `enum Box[A]`, definitions over them, and induction.
 *
 *  This is what the tactic-engine fix in v0.7 unlocked. Before it,
 *  `Builtins.buildFixCase` extended a branch context with raw constructor
 *  argument types that still mentioned the enum's type parameters, so those
 *  indices pointed at `_n` and `_rec` instead — a generic enum could be declared
 *  but nothing inductive could be proved about it.
 */
class GenericEnumSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private val genericList =
    """@proofModule
      |object M:
      |  enum Nat:
      |    case Zero
      |    case Succ(n: Nat)
      |
      |  enum Lst[A]:
      |    case Nil()
      |    case Cons(head: A, tail: Lst[A])
      |
      |  import Nat.*, Lst.*
      |
      |  def append[A](xs: Lst[A], ys: Lst[A]): Lst[A] =
      |    xs match
      |      case Nil()       => ys
      |      case Cons(h, t)  => Cons(h, append(t, ys))
      |
      |  def copy[A](xs: Lst[A]): Lst[A] =
      |    xs match
      |      case Nil()      => Nil()
      |      case Cons(h, t) => Cons(h, copy(t))
      |
      |%THEOREMS%
      |""".stripMargin

  test("a generic enum with definitions over it compiles") {
    val result = CompilerHarness.compileModule(genericList.replace("%THEOREMS%",
      """  @theorem
        |  def appendNilLeft[A](ys: Lst[A]): Proof =
        |    prove(append(Nil[A](), ys) === ys)(trivial)
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("induction over a generic enum works, with the hypothesis") {
    val result = CompilerHarness.compileModule(genericList.replace("%THEOREMS%",
      """  @theorem
        |  def appendNilRight[A](xs: Lst[A]): Proof =
        |    prove(append(xs, Nil[A]()) === xs)(
        |      induction(xs) {
        |        case Nil()      => trivial
        |        case Cons(h, t) => simplify(ih(t))
        |      })
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a second inductive theorem over the same generic enum") {
    val result = CompilerHarness.compileModule(genericList.replace("%THEOREMS%",
      """  @theorem
        |  def copyId[A](xs: Lst[A]): Proof =
        |    prove(copy(xs) === xs)(
        |      induction(xs) {
        |        case Nil()      => trivial
        |        case Cons(h, t) => simplify(ih(t))
        |      })
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a false theorem over a generic enum is still rejected") {
    val result = CompilerHarness.compileModule(genericList.replace("%THEOREMS%",
      """  @theorem
        |  def bogus[A](xs: Lst[A], ys: Lst[A]): Proof =
        |    prove(append(xs, ys) === xs)(
        |      induction(xs) {
        |        case Nil()      => trivial
        |        case Cons(h, t) => simplify(ih(t))
        |      })
        |""".stripMargin))
    assert(result.failed, s"a false generic theorem was accepted:\n${result.report}")
    assert(result.hasSroofError, result.report)
    assert(result.mentions("theorem bogus"), result.report)
  }

  test("a generic enum instantiated at a concrete type is supported") {
    val result = CompilerHarness.compileModule(genericList.replace("%THEOREMS%",
      """  def natList: Lst[Nat] = Cons(Zero, Nil[Nat]())
        |
        |  @theorem
        |  def copyNatList: Proof = prove(copy(natList) === natList)(trivial)
        |""".stripMargin))
    assert(result.succeeded, result.report)
  }

  test("a non-generic enum still works alongside a generic one") {
    val result = CompilerHarness.compileModule(genericList.replace("%THEOREMS%",
      """  def plus(n: Nat, m: Nat): Nat =
        |    n match
        |      case Zero    => m
        |      case Succ(k) => Succ(plus(k, m))
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
