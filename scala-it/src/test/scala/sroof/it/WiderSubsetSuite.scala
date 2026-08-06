package sroof.it

import munit.FunSuite

/** The subset added in v0.4: curried parameter lists, runs of local `val`s,
 *  constructors whose recursive field follows other fields, and the `cases` and
 *  `rewrite` tactics.
 *
 *  Each widening is tested from both sides — what it now accepts, and what it
 *  still refuses — because a widening that quietly swallowed the neighbouring
 *  invalid case would be worse than no widening at all.
 */
class WiderSubsetSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private def accepts(body: String): Unit =
    val result = CompilerHarness.compileModule(body)
    assert(result.succeeded, result.report)

  private def rejects(body: String)(fragment: String): Unit =
    val result = CompilerHarness.compileModule(body)
    assert(result.failed, s"expected compilation to fail, but it succeeded:\n$body")
    assert(result.hasSroofError, s"failure did not come from sroof:\n${result.report}")
    assert(result.mentions(fragment), result.report)

  // ---- curried parameter lists ----

  test("a definition with curried parameter lists is supported") {
    accepts(Fixtures.module(
      """  def add(n: Nat)(m: Nat): Nat = plus(n, m)
        |
        |  @theorem
        |  def addZeroLeft(m: Nat): Proof =
        |    prove(add(Zero)(m) === m)(trivial)
        |""".stripMargin))
  }

  test("a theorem with curried parameter lists is supported") {
    accepts(Fixtures.module(
      """  @theorem
        |  def plusSuccLeft(n: Nat)(m: Nat): Proof =
        |    prove(plus(Succ(n), m) === Succ(plus(n, m)))(trivial)
        |""".stripMargin))
  }

  test("a partially applied call is rejected") {
    rejects(Fixtures.module(
      """  def add(n: Nat)(m: Nat): Nat = plus(n, m)
        |  def partial(n: Nat): Nat = add(n)(Zero)
        |
        |  def broken(n: Nat): Nat =
        |    val f: Nat => Nat = add(n)
        |    f(Zero)
        |
        |  @theorem
        |  def thm(m: Nat): Proof = prove(plus(Zero, m) === m)(trivial)
        |""".stripMargin))("verified definition broken")
  }

  // ---- runs of local vals ----

  test("several sequential local vals are supported") {
    accepts(Fixtures.module(
      """  def thrice(n: Nat): Nat =
        |    val a: Nat = plus(n, Zero)
        |    val b: Nat = plus(a, Zero)
        |    val c: Nat = plus(b, Zero)
        |    c
        |
        |  @theorem
        |  def thriceZero: Proof = prove(thrice(Zero) === Zero)(trivial)
        |""".stripMargin))
  }

  test("a later val may refer to an earlier one") {
    accepts(Fixtures.module(
      """  def chained(n: Nat): Nat =
        |    val once: Nat  = plus(n, Zero)
        |    val twice: Nat = plus(once, once)
        |    twice
        |
        |  @theorem
        |  def chainedZero: Proof = prove(chained(Zero) === Zero)(trivial)
        |""".stripMargin))
  }

  test("a var among the vals is still rejected") {
    rejects(Fixtures.module(
      """  def sneaky(n: Nat): Nat =
        |    val a: Nat = n
        |    var b: Nat = a
        |    b
        |
        |  @theorem
        |  def thm(m: Nat): Proof = prove(plus(Zero, m) === m)(trivial)
        |""".stripMargin))("verified definition sneaky")
  }

  // ---- recursive field after other fields ----

  test("a constructor whose last field is recursive supports induction with ih") {
    accepts(
      """@proofModule
        |object M:
        |  enum Tag:
        |    case A
        |    case B
        |
        |  enum Tagged:
        |    case Empty
        |    case Cons(tag: Tag, rest: Tagged)
        |
        |  import Tag.*, Tagged.*
        |
        |  def size(t: Tagged): Tagged =
        |    t match
        |      case Empty        => Empty
        |      case Cons(_, rest) => Cons(A, size(rest))
        |
        |  @theorem
        |  def sizeIdempotent(t: Tagged): Proof =
        |    prove(size(size(t)) === size(t))(
        |      induction(t) {
        |        case Empty         => trivial
        |        case Cons(_, rest) => simplify(ih(rest))
        |      })
        |""".stripMargin)
  }

  test("ih on a non-final field is rejected") {
    rejects(
      """@proofModule
        |object M:
        |  enum Pair2:
        |    case Leaf
        |    case Node(left: Pair2, right: Pair2)
        |
        |  import Pair2.*
        |
        |  def mirror(p: Pair2): Pair2 =
        |    p match
        |      case Leaf         => Leaf
        |      case Node(l, r)   => Node(mirror(r), mirror(l))
        |
        |  @theorem
        |  def thm(p: Pair2): Proof =
        |    prove(p === p)(
        |      induction(p) {
        |        case Leaf       => trivial
        |        case Node(l, r) => simplify(ih(l))
        |      })
        |""".stripMargin)("last (recursive) field")
  }

  test("ih on an unnamed recursive field asks for a binder") {
    rejects(Fixtures.module(
      """  @theorem
        |  def thm(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(_) => simplify(ih(n))
        |      })
        |""".stripMargin))("bound to a name")
  }

  // ---- cases ----

  test("cases splits on constructors without a hypothesis") {
    accepts(Fixtures.module(
      """  @theorem
        |  def plusZeroLeftBoth(n: Nat): Proof =
        |    prove(plus(Zero, n) === n)(
        |      cases(n) {
        |        case Zero    => trivial
        |        case Succ(k) => trivial
        |      })
        |""".stripMargin))
  }

  test("ih inside cases is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def thm(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      cases(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin))("generates no induction")
  }

  test("cases must still cover every constructor") {
    rejects(Fixtures.module(
      """  @theorem
        |  def thm(n: Nat): Proof =
        |    prove(plus(Zero, n) === n)(
        |      cases(n) {
        |        case Zero => trivial
        |      })
        |""".stripMargin))("missing branch")
  }

  // ---- rewrite ----

  test("rewrite closes a goal using the induction hypothesis") {
    accepts(Fixtures.module(
      """  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => rewrite(ih(k))
        |      })
        |""".stripMargin))
  }

  test("rewrite with a lemma that does not apply still fails the proof") {
    rejects(Fixtures.module(
      """  @theorem
        |  def bogus(n: Nat): Proof =
        |    prove(plus(n, Zero) === Succ(n))(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => rewrite(ih(k))
        |      })
        |""".stripMargin))("theorem bogus")
  }

  // ---- no-argument simplify ----

  test("simplify() with no lemmas uses the @simp set") {
    accepts(Fixtures.module(
      """  @simp
        |  @theorem
        |  def plusZeroRight(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |
        |  @theorem
        |  def again(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(simplify())
        |""".stripMargin))
  }
