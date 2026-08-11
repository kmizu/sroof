package sroof

import munit.FunSuite

/** `calc` chains.
  *
  * A multi-step chain never worked: `buildTransProof` was handed the midpoint
  * *term* where the transitivity motive needed its **type**, producing a binder
  * `λy:Nat.zero. …`, and the motive body used the 3-argument `Eq` form with a
  * `Meta` element type — which `inferUniverse` does not recognise and the
  * evaluator refuses outright. The result was a beta-redex the checker could not
  * reduce and a rejection of every correct chain.
  *
  * A single-step chain returns before reaching that code, which is why the tactic
  * looked like it worked.
  */
class CalcSuite extends FunSuite:

  private val nat =
    """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
       |def plus(a: Nat, b: Nat): Nat {
       |  match a {
       |    case Nat.zero    => b
       |    case Nat.succ(k) => Nat.succ(plus(k, b))
       |  }
       |}
       |""".stripMargin

  private def check(body: String) = Main.processSource(nat + body, "calc.sroof")

  test("a single-step chain is accepted"):
    // The path that always worked. Kept so that a fix to the multi-step case
    // that broke this one would be visible.
    val r = check(
      """|defspec t: Nat.zero = Nat.zero {
         |  by calc { Nat.zero = Nat.zero { by trivial } }
         |}
         |""".stripMargin)
    assert(r.isRight, s"expected acceptance, got: $r")

  test("a two-step chain is accepted"):
    val r = check(
      """|defspec t: Nat.zero = Nat.zero {
         |  by calc {
         |    Nat.zero = Nat.zero { by trivial }
         |    _ = Nat.zero { by trivial }
         |  }
         |}
         |""".stripMargin)
    assert(r.isRight, s"expected acceptance, got: $r")

  test("a chain whose steps do real work is accepted"):
    // Not just `zero = zero` twice: each step is a distinct reduction, so the
    // transitivity term actually has to connect two different equations.
    val r = check(
      """|defspec chain:
         |    plus(Nat.succ(Nat.zero), Nat.succ(Nat.zero)) = Nat.succ(Nat.succ(Nat.zero)) {
         |  by calc {
         |    plus(Nat.succ(Nat.zero), Nat.succ(Nat.zero))
         |      = Nat.succ(plus(Nat.zero, Nat.succ(Nat.zero))) { by trivial }
         |    _ = Nat.succ(Nat.succ(Nat.zero)) { by trivial }
         |  }
         |}
         |""".stripMargin)
    assert(r.isRight, s"expected acceptance, got: $r")

  test("SOUNDNESS: a step that does not hold is rejected"):
    val r = check(
      """|defspec bad: Nat.zero = Nat.succ(Nat.zero) {
         |  by calc {
         |    Nat.zero = Nat.zero { by trivial }
         |    _ = Nat.succ(Nat.zero) { by trivial }
         |  }
         |}
         |""".stripMargin)
    assert(r.isLeft, s"a false step must be rejected, got: $r")

  test("SOUNDNESS: a chain that does not reach the goal is rejected"):
    // The chain proves `zero = zero`; the goal is `zero = succ zero`. Accepting
    // this would mean the chain's endpoints are never compared with the goal.
    val r = check(
      """|defspec bad: Nat.zero = Nat.succ(Nat.zero) {
         |  by calc { Nat.zero = Nat.zero { by trivial } }
         |}
         |""".stripMargin)
    assert(r.isLeft, s"a chain that misses the goal must be rejected, got: $r")
