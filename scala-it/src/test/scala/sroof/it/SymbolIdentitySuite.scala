package sroof.it

import munit.FunSuite

/** The plugin must recognise the DSL by resolved symbol, never by name.
 *
 *  If recognition were textual, a user's own `trivial` or `===` could be read as
 *  a proof step — which would let unverified code masquerade as a theorem.  Each
 *  test here defines a same-named impostor and asserts it is treated as ordinary
 *  Scala or rejected, but never as the sroof DSL.
 */
class SymbolIdentitySuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  test("a user-defined `trivial` is not the sroof tactic") {
    // `myTrivial.trivial` has the right name and even the right type, but a
    // different symbol.  Accepting it would mean proving nothing.
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def sneaky(n: Nat): Proof =
        |    prove(plus(n, Zero) === Succ(n))(Impostor.trivial)
        |""".stripMargin) +
      """
        |object Impostor:
        |  def trivial: sroof.lang.Tactic = sroof.lang.trivial
        |""".stripMargin)
    assert(result.failed, s"an impostor `trivial` was accepted:\n${result.report}")
    assert(result.hasSroofError, result.report)
    assert(result.mentions("unsupported tactic"), result.report)
  }

  test("a user-defined `prove` is not the sroof prove") {
    // The impostor lives outside the module so that it is not rejected merely
    // as unsupported verified code: the point is that a theorem body calling it
    // is not recognised as a proof.
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def sneaky(n: Nat): Proof = Impostor.prove(Zero)(Zero)
        |""".stripMargin) +
      """
        |object Impostor:
        |  def prove(goal: M.Nat)(tactic: M.Nat): sroof.lang.Proof =
        |    sroof.lang.prove(sroof.lang.===(goal)(goal))(sroof.lang.trivial)
        |""".stripMargin)
    assert(result.failed, s"an impostor `prove` was accepted:\n${result.report}")
    assert(result.hasSroofError, result.report)
    assert(result.mentions("prove(goal)(tactic)"), result.report)
  }

  test("a user-defined `===` is not the sroof equality") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def sneaky(n: Nat): Proof =
        |    prove(Impostor.===(plus(n, Zero), Succ(n)))(trivial)
        |""".stripMargin) +
      """
        |object Impostor:
        |  def ===(a: M.Nat, b: M.Nat): sroof.lang.Prop = sroof.lang.===(a)(a)
        |""".stripMargin)
    assert(result.failed, s"an impostor `===` was accepted:\n${result.report}")
    assert(result.hasSroofError, result.report)
    assert(result.mentions("must be an equality built with sroof"), result.report)
  }

  test("a user-defined `simplify` is not the sroof tactic") {
    val result = CompilerHarness.compileModule(Fixtures.module(
      """  @theorem
        |  def sneaky(n: Nat): Proof =
        |    prove(plus(n, Zero) === Succ(n))(Impostor.simplify())
        |""".stripMargin) +
      """
        |object Impostor:
        |  def simplify(lemmas: sroof.lang.Proof*): sroof.lang.Tactic = sroof.lang.trivial
        |""".stripMargin)
    assert(result.failed, s"an impostor `simplify` was accepted:\n${result.report}")
    assert(result.hasSroofError, result.report)
    assert(result.mentions("unsupported tactic"), result.report)
  }

  test("a user-defined `theorem` annotation does not trigger verification") {
    // A same-named annotation from another package must not make the plugin
    // treat this as a theorem — nor must the method be silently accepted as one.
    val result = CompilerHarness.compileModule(
      """object mine:
        |  final class theorem extends scala.annotation.StaticAnnotation
        |
        |@proofModule
        |object M:
        |  enum Nat:
        |    case Zero
        |    case Succ(n: Nat)
        |  import Nat.*
        |
        |  @mine.theorem
        |  def notATheorem(n: Nat): Nat = n
        |""".stripMargin)
    // `notATheorem` is treated as an ordinary verified definition (it is one),
    // so the module verifies and compilation succeeds.
    assert(result.succeeded, result.report)
  }
