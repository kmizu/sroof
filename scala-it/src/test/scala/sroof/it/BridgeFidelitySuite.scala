package sroof.it

import munit.FunSuite

/** Does a Scala theorem mean what the Scala says?
  *
  * The kernel cannot answer that. It checks a proof against the core proposition
  * the bridge produced, so a bridge that translated `sub(a, b)` as `sub(b, a)`
  * would hand it a valid proof of a different statement and nothing downstream
  * would notice.
  *
  * So every case here is a **false** statement built out of one construct. If the
  * construct is translated faithfully the statement stays false and compilation
  * fails; if it is mistranslated the statement may become true and compile. Each
  * false case is paired with a true control, because a bridge that rejected
  * everything would pass the false half on its own.
  */
class BridgeFidelitySuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(600, "s")

  private def accepts(label: String, body: String): Unit =
    val r = CompilerHarness.compileModule(body)
    assert(!r.failed, s"$label: expected acceptance, got:\n${r.report}")

  private def rejects(label: String, body: String): Unit =
    val r = CompilerHarness.compileModule(body)
    assert(r.failed, s"$label: expected rejection, but it compiled:\n$body")
    assert(r.hasSroofError, s"$label: rejected, but not by sroof:\n${r.report}")

  // ---- argument order ----

  private def subModule(claim: String): String = Fixtures.module(
    s"""  def sub(n: Nat, m: Nat): Nat =
       |    m match
       |      case Zero    => n
       |      case Succ(k) => Zero
       |
       |  @theorem
       |  def t: Proof = prove($claim)(trivial)
       |""".stripMargin)

  test("argument order is preserved"):
    // `sub` is deliberately asymmetric: sub(Succ(Zero), Zero) is Succ(Zero) and
    // sub(Zero, Succ(Zero)) is Zero. Swapping the arguments in translation would
    // flip which of these two theorems holds, so the pair pins the order.
    accepts("true order", subModule("sub(Succ(Zero), Zero) === Succ(Zero)"))
    rejects("swapped order", subModule("sub(Zero, Succ(Zero)) === Succ(Zero)"))

  // ---- nested application ----

  test("a nested call computes what Scala computes"):
    accepts("true", Fixtures.module(
      """  @theorem
        |  def t: Proof = prove(plus(Succ(Zero), Succ(Zero)) === Succ(Succ(Zero)))(trivial)
        |""".stripMargin))
    rejects("false", Fixtures.module(
      """  @theorem
        |  def t: Proof = prove(plus(Succ(Zero), Succ(Zero)) === Succ(Zero))(trivial)
        |""".stripMargin))

  // ---- val bindings ----

  private def valModule(claim: String): String = Fixtures.module(
    s"""  def twice(n: Nat): Nat =
       |    val once = plus(n, Zero)
       |    plus(once, n)
       |
       |  @theorem
       |  def t: Proof = prove($claim)(trivial)
       |""".stripMargin)

  test("a val binding keeps its definition"):
    // A binding dropped or bound to the wrong expression would change what
    // `twice(Succ(Zero))` reduces to.
    accepts("true", valModule("twice(Succ(Zero)) === Succ(Succ(Zero))"))
    rejects("false", valModule("twice(Succ(Zero)) === Zero"))

  // ---- default arguments ----

  private def defaultArgModule(claim: String): String = Fixtures.module(
    s"""  def addZ(n: Nat, m: Nat = Zero): Nat = plus(n, m)
       |
       |  @theorem
       |  def t: Proof = prove($claim)(trivial)
       |""".stripMargin)

  test("a default argument supplies the declared default"):
    // `addZ(Succ(Zero))` is `Succ(Zero)` only if the omitted argument becomes
    // `Zero`. A translation that dropped the parameter, or filled it with the
    // first argument, would give a different answer.
    accepts("true, omitted", defaultArgModule("addZ(Succ(Zero)) === Succ(Zero)"))
    rejects("false, omitted", defaultArgModule("addZ(Succ(Zero)) === Zero"))
    accepts("true, explicit", defaultArgModule("addZ(Zero, Succ(Zero)) === Succ(Zero)"))
    rejects("false, explicit", defaultArgModule("addZ(Zero, Succ(Zero)) === Zero"))

  // ---- what is outside the subset ----

  test("a lambda is rejected rather than approximated"):
    rejects("lambda", Fixtures.module(
      """  def apply1(f: Nat => Nat, n: Nat): Nat = f(n)
        |
        |  @theorem
        |  def t: Proof = prove(apply1(x => x, Zero) === Zero)(trivial)
        |""".stripMargin))

  test("a side effect is rejected rather than ignored"):
    rejects("println", Fixtures.module(
      """  def noisy(n: Nat): Nat =
        |    println("hello")
        |    n
        |
        |  @theorem
        |  def t: Proof = prove(noisy(Zero) === Zero)(trivial)
        |""".stripMargin))

  test("if/else is rejected in both directions"):
    // Not supported, so the *true* statement is rejected too. That is the point:
    // an unsupported construct is refused, not approximated into something that
    // happens to agree on this example.
    val mod = (claim: String) => Fixtures.module(
      s"""  def pick(b: Boolean, n: Nat): Nat = if b then n else Zero
         |
         |  @theorem
         |  def t: Proof = prove($claim)(trivial)
         |""".stripMargin)
    rejects("if/else, true claim",  mod("pick(true, Succ(Zero)) === Succ(Zero)"))
    rejects("if/else, false claim", mod("pick(true, Succ(Zero)) === Zero"))

  // ---- GADTs ----

  private val natEnum =
    """  enum Nat:
      |    case Zero
      |    case Succ(n: Nat)
      |
      |  import Nat.*
      |""".stripMargin

  test("a GADT case is rejected rather than having its index dropped"):
    // `valueParams` instantiates every case at the *enum's* type parameters, so
    // `VNil` and `VCons` would both become constructors of a uniform `Vec[A, N]`
    // and the index would silently mean nothing. The core does support indexed
    // families; this is a gap in the bridge, and the bridge refuses what it
    // cannot carry.
    val r = CompilerHarness.compileModule(Fixtures.bareModule(
      natEnum +
      """
        |  enum Vec[A, N]:
        |    case VNil[A]()                       extends Vec[A, Zero.type]
        |    case VCons[A, M](h: A, t: Vec[A, M]) extends Vec[A, Succ]
        |
        |  @theorem
        |  def t: Proof = prove(Zero === Zero)(trivial)
        |""".stripMargin))
    assert(r.failed, "a GADT-shaped enum must be rejected")
    assert(r.hasSroofError, s"rejected, but not by sroof:\n${r.report}")
    assert(
      r.mentions("GADT") || r.mentions("fixes a type argument"),
      s"the diagnostic must say what is unsupported:\n${r.report}",
    )

  test("an ordinary generic enum is still accepted (control)"):
    // Without this, a check that rejected every generic enum would pass above.
    accepts("generic enum", Fixtures.bareModule(
      natEnum +
      """
        |  enum Box[A]:
        |    case Wrap(a: A)
        |
        |  @theorem
        |  def t: Proof = prove(Zero === Zero)(trivial)
        |""".stripMargin))
