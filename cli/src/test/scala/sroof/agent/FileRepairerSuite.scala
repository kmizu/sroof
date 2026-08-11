package sroof.agent

import munit.FunSuite
import sroof.Main

/** What `sroof agent` writes back.
  *
  * `SearchLoopSuite` covers the search. This covers the part a user sees: the file
  * that comes out. Two things have to hold and nothing tested either.
  *
  *   1. The output is a file the checker accepts. The agent renders a found tactic
  *      back to source text, and a rendering that dropped a brace or mis-indented a
  *      case would still be reported as `[OK]` per theorem while leaving a file that
  *      does not parse.
  *   2. A statement that is false is not "repaired". The agent is a tactic
  *      generator, so anything it produces is checked by the kernel — but a bug that
  *      wrote *some* tactic into the file regardless would turn a loud `sorry` into
  *      a quiet failure somewhere else.
  */
class FileRepairerSuite extends FunSuite:

  private val prelude =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |
       |def plus(a: Nat, b: Nat): Nat {
       |  match a {
       |    case Nat.zero    => b
       |    case Nat.succ(k) => Nat.succ(plus(k, b))
       |  }
       |}
       |""".stripMargin

  private def theorem(name: String, stmt: String) =
    s"""|defspec $name(n: Nat): $stmt {
        |  by sorry
        |}
        |""".stripMargin

  test("a repaired file parses and verifies"):
    val src      = prelude + theorem("plus_zero", "plus(n, Nat.zero) = n")
    val repaired = FileRepairer.repair(src, "t.sroof")
    assert(!repaired.contains("sorry"), s"the sorry should be gone:\n$repaired")
    val r = Main.processSource(repaired, "t.sroof")
    assert(r.isRight, s"the agent wrote a file the checker rejects:\n$repaired\n$r")

  test("a false statement is left as sorry"):
    // `plus(n, succ zero)` is `succ n`, never `n`. Nothing the agent generates can
    // close this, and it must not claim otherwise.
    val src      = prelude + theorem("bogus", "plus(n, Nat.succ(Nat.zero)) = n")
    val results  = FileRepairer.tryRepair(src, "t.sroof")
    assertEquals(results.map(_.defspecName), List("bogus"))
    assert(!results.head.succeeded, s"a false statement was 'proved': ${results.head.found}")
    assertEquals(FileRepairer.repair(src, "t.sroof"), src)

  test("a partial repair fixes what it can and keeps the rest"):
    val src = prelude +
      theorem("plus_zero", "plus(n, Nat.zero) = n") +
      theorem("bogus",     "plus(n, Nat.succ(Nat.zero)) = n") +
      theorem("plus_zero_left", "plus(Nat.zero, n) = n")
    val results = FileRepairer.tryRepair(src, "t.sroof")
    assertEquals(results.filter(_.succeeded).map(_.defspecName), List("plus_zero", "plus_zero_left"))
    val repaired = FileRepairer.repair(src, "t.sroof")
    // Exactly one `sorry` survives, and the file still checks — with a warning.
    assertEquals(repaired.sliding("sorry".length).count(_ == "sorry"), 1)
    val r = Main.processSource(repaired, "t.sroof")
    assert(r.isRight, s"the partially repaired file must still check:\n$repaired\n$r")

  test("a file with no sorry is returned unchanged"):
    val src = prelude +
      """|defspec plus_zero_left(n: Nat): plus(Nat.zero, n) = n {
         |  by trivial
         |}
         |""".stripMargin
    assertEquals(FileRepairer.tryRepair(src, "t.sroof"), Nil)
    assertEquals(FileRepairer.repair(src, "t.sroof"), src)
