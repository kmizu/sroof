package sroof

import munit.FunSuite

/** `--fail-on-sorry` has one job, and it could be walked past.
  *
  * `countSorryTactic` ended in `case _ => 0`, and three tactics that carry a proof
  * fell into it: `obtain` and `specialize` each continue into another tactic, and
  * `calc` holds a proof per step. A `sorry` in any of them counted as zero, so the
  * file printed a plain `OK` with **no warning at all** and `--fail-on-sorry`
  * exited 0 — on a file containing the word `sorry`.
  *
  * The count also drives `skipKernel`, so the placeholder stopped behaving like a
  * placeholder: the proof went to the kernel, which rejected it with a type
  * mismatch about a term the author never wrote.
  *
  * The catch-all is gone; every tactic is enumerated, so the next one added fails
  * to compile here instead of silently reporting no `sorry`.
  */
class SorryGateSuite extends FunSuite:

  private val prelude =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |""".stripMargin

  private def warnings(src: String): String =
    Main.processSourceJson(prelude + src, "t.sroof")

  private def assertReported(src: String, label: String): Unit =
    val js = warnings(src)
    assert(js.contains("uses sorry"),
      s"$label: a file containing sorry produced no warning:\n$js")
    assert(Main.processSourceJson(prelude + src, "t.sroof", failOnSorry = true)
             .contains("\"ok\":false"),
      s"$label: --fail-on-sorry did not fail on a file containing sorry")

  test("sorry in a specialize continuation is reported"):
    assertReported(
      """|defspec hidden(h: Nat -> Nat): Nat.zero = Nat.zero {
         |  by specialize h Nat.zero ; sorry
         |}
         |""".stripMargin, "specialize")

  test("sorry in a calc step is reported"):
    assertReported(
      """|defspec hidden(): Nat.zero = Nat.zero {
         |  by calc { Nat.zero = Nat.zero { by sorry } }
         |}
         |""".stripMargin, "calc")

  test("a plain sorry is still reported"):
    // The control. A fix that reported nothing would fail this, and a fix that
    // reported everything would fail the next one.
    assertReported(
      "defspec plain(): Nat.zero = Nat.zero { by sorry }\n", "plain")

  test("a file with no sorry is not reported"):
    val js = warnings("defspec fine(): Nat.zero = Nat.zero { by trivial }\n")
    assert(!js.contains("uses sorry"), s"a sorry-free file was reported:\n$js")
    assert(js.contains("\"ok\":true"), s"a sorry-free file did not check:\n$js")
