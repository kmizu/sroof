package sroof

import munit.FunSuite

/** The file that proved `0 = 1`.
  *
  * Measured on the previous tree, this exact source printed
  * `OK: … — 2 inductive(s), 1 definition(s), 1 defspec(s)` and exited **0**. No
  * warning, no `sorry`, no hang: a false theorem with a green check on it.
  *
  * The route is short. `TerminationChecker.checkBody` walked a match's branches
  * and never looked at its scrutinee, so `match toEmpty(n) { }` — a recursive
  * call with nothing guarding it, and no branch to be found in — was accepted.
  * That gives `toEmpty : Nat -> Empty`, and `match toEmpty(zero) { }` has
  * whatever type you ask for. The kernel checks the proof term by *type*; it
  * never runs `toEmpty`, so nothing diverges and nothing complains.
  *
  * The kernel could not have caught this: `Kernel.verify` is asked whether a
  * term has a claimed type, and this term does. Termination is the front end's
  * to enforce — which is why the front end's version of it has to be right.
  */
class TerminationGateSuite extends FunSuite:

  private val prelude =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |inductive Empty {
       |}
       |""".stripMargin

  private def json(src: String) = Main.processSourceJson(prelude + src, "t.sroof")

  test("the file that proved 0 = 1 is rejected"):
    val js = json(
      """|def toEmpty(n: Nat): Empty {
         |  match toEmpty(n) {
         |  }
         |}
         |defspec zero_is_one: Nat.zero = Nat.succ(Nat.zero) {
         |  by exact match toEmpty(Nat.zero) { }
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":false"), s"a proof of 0 = 1 was accepted:\n$js")
    assert(js.contains("Termination check failed"),
      s"rejected, but not for being non-terminating — the gate may not be what stopped it:\n$js")

  test("a recursive call in the scrutinee is rejected on its own"):
    // Without the defspec, so the failure is the definition and not the proof.
    val js = json(
      """|def scrutloop(n: Nat): Nat {
         |  match scrutloop(n) {
         |    case Nat.zero    => Nat.zero
         |    case Nat.succ(k) => Nat.zero
         |  }
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":false"), s"an unguarded recursive call was accepted:\n$js")
    assert(js.contains("scrutinee"), s"the message does not say where the call is:\n$js")

  test("a smaller argument in the wrong position is rejected"):
    // `k` is a subterm of `m`, so "some argument is smaller" was satisfied. But
    // `m` is passed back unchanged in the position that was matched on, so the
    // next call sees the same `m`. Measured on the previous tree: accepted, and
    // then StackOverflowError when a defspec forced it to evaluate.
    val js = json(
      """|def loop(n: Nat, m: Nat): Nat {
         |  match m {
         |    case Nat.zero    => Nat.zero
         |    case Nat.succ(k) => loop(k, m)
         |  }
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":false"), s"a function that loops forever was accepted:\n$js")
    assert(js.contains("Termination check failed"), s"rejected for the wrong reason:\n$js")

  test("ordinary recursion still checks"):
    // The control. A gate that rejected every recursive definition would pass
    // all three tests above and make the language useless.
    val js = json(
      """|def plus(n: Nat, m: Nat): Nat {
         |  match n {
         |    case Nat.zero    => m
         |    case Nat.succ(k) => Nat.succ(plus(k, m))
         |  }
         |}
         |defspec plus_zero(n: Nat): plus(Nat.zero, n) = n {
         |  by trivial
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":true"), s"an ordinary recursive definition was rejected:\n$js")

  test("recursion on the second argument still checks"):
    // The other control, and the sharper one: the fix pins the decreasing
    // position to whichever parameter the match takes apart, so it must not
    // have quietly become "the first parameter".
    val js = json(
      """|def countdown(acc: Nat, m: Nat): Nat {
         |  match m {
         |    case Nat.zero    => acc
         |    case Nat.succ(k) => countdown(Nat.succ(acc), k)
         |  }
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":true"), s"recursion on the second argument was rejected:\n$js")
