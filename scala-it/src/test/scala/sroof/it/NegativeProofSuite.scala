package sroof.it

import munit.FunSuite

/** Proofs that must not be accepted.
 *
 *  Each case asserts three things: the compilation failed, the failure came
 *  from sroof, and the message is specific enough to act on.  A test that only
 *  checked "compilation failed" would pass even if the plugin crashed.
 */
class NegativeProofSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private def rejects(body: String)(check: CompilerHarness.Result => Unit): Unit =
    val result = CompilerHarness.compileModule(body)
    assert(result.failed, s"expected compilation to fail, but it succeeded:\n$body")
    assert(result.hasSroofError, s"failure did not come from sroof:\n${result.report}")
    check(result)

  test("a false theorem attempted with trivial is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def bogus(n: Nat): Proof =
        |    prove(plus(n, Zero) === Succ(n))(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("theorem bogus"), r.report)
      assert(r.mentions("not definitionally equal"), r.report)
    }
  }

  test("a false inductive theorem is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def bogusInd(n: Nat): Proof =
        |    prove(plus(n, Zero) === Succ(n))(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("theorem bogusInd"), r.report)
    }
  }

  test("ih in a base case is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def badIh(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => simplify(ih(n))
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("base case"), r.report)
    }
  }

  test("ih applied to the wrong binder is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def badIh(n: Nat, m: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(m))
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("recursive field"), r.report)
    }
  }

  test("a theorem body that is not prove(goal)(tactic) is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def notAProof(n: Nat): Proof = trivialProof
        |
        |  def trivialProof: Proof = prove(Zero === Zero)(trivial)
        |""".stripMargin)) { r =>
      assert(r.mentions("prove(goal)(tactic)") || r.mentions("Proof"), r.report)
    }
  }

  test("a theorem outside a @proofModule is rejected") {
    val result = CompilerHarness.compileModule(
      """object NotAProofModule:
        |  @theorem
        |  def orphan: Proof = prove(NotAProofModule.hashCode() === 1)(trivial)
        |""".stripMargin)
    assert(result.failed, result.report)
    assert(result.hasSroofError, result.report)
    assert(result.mentions("only verified inside a @proofModule"), result.report)
  }

  test("a theorem returning the wrong result type is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def wrongType(n: Nat): Nat = Zero
        |""".stripMargin)) { r =>
      assert(r.mentions("must return exactly sroof.lang.Proof"), r.report)
    }
  }

  test("an induction missing a constructor branch is rejected") {
    // Scala's own exhaustivity check warns rather than errors for a
    // PartialFunction, so this must be caught by sroof.
    rejects(Fixtures.module(
      """  @theorem
        |  def missingBranch(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero => trivial
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("missing branch"), r.report)
    }
  }

  test("an induction with a duplicate constructor branch is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def duplicateBranch(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero    => trivial
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("duplicate branch"), r.report)
    }
  }

  test("a pattern binder named `ih` is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def shadowed(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(n) {
        |        case Zero     => trivial
        |        case Succ(ih) => trivial
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("reserved for the generated induction hypothesis"), r.report)
    }
  }

  test("an induction target that is not a theorem parameter is rejected") {
    rejects(Fixtures.module(
      """  @theorem
        |  def notAParam(n: Nat): Proof =
        |    prove(plus(n, Zero) === n)(
        |      induction(Zero) {
        |        case Zero    => trivial
        |        case Succ(k) => simplify(ih(k))
        |      })
        |""".stripMargin)) { r =>
      assert(r.mentions("must be a parameter of this theorem"), r.report)
    }
  }
