package sroof

import munit.FunSuite
import sroof.core.GlobalEnv
import scala.collection.mutable.ListBuffer

/** The REPL, driven from a script instead of a terminal.
  *
  * Nothing tested it before. `MainSuite` had a case called "readMultiLine:
  * single-line input terminates after one non-empty line" whose body says it cannot
  * test stdin and calls `processSource` instead — so the reader itself, and the loop
  * around it, were unexercised.
  *
  * They needed to be. `readMultiLine` returned `""` both for a blank line and for
  * end of input, and the loop ignores blank input; `sroof repl < script.sroof`
  * therefore printed a prompt and read again, forever, at a rate of about a megabyte
  * of prompts a second.
  *
  * Every fake reader here fails the test rather than returning `null` forever, so a
  * regression to that loop shows up as a failure instead of a hung build.
  */
class ReplSuite extends FunSuite:

  /** A reader over a fixed script that refuses to be read past the end for long. */
  private def scripted(lines: String*): String => String =
    val it = lines.iterator
    var past = 0
    _ =>
      if it.hasNext then it.next()
      else
        past += 1
        if past > 100 then fail("the REPL kept reading after end of input")
        null

  private def session(lines: String*): List[String] =
    val out = ListBuffer.empty[String]
    given GlobalEnv = GlobalEnv.empty
    Main.runRepl(scripted(lines*), out += _)
    out.toList

  test("end of input ends the session"):
    val out = session("inductive Nat { case zero: Nat  case succ(n: Nat): Nat }")
    assert(out.exists(_.contains("inductive: Nat")), s"the declaration should land: $out")
    assertEquals(out.last, "Goodbye.")

  test("end of input with nothing typed ends the session"):
    assertEquals(session().last, "Goodbye.")

  test("a blank line is ignored and does not end the session"):
    // The distinction the bug erased: blank input is skipped, end of input stops.
    val out = session("", "", "inductive Bool { case tru: Bool  case fls: Bool }")
    assert(out.exists(_.contains("inductive: Bool")), s"input after blanks should land: $out")

  test(":quit ends the session before the rest of the script"):
    val out = session(":quit", "inductive Never { case n: Never }")
    assertEquals(out.last, "Goodbye.")
    assert(!out.exists(_.contains("Never")), s"nothing after :quit should run: $out")

  test("definitions accumulate across entries"):
    val out = session(
      "inductive Nat { case zero: Nat  case succ(n: Nat): Nat }",
      "def one(): Nat { Nat.succ(Nat.zero) }",
    )
    assert(out.exists(_.contains("defined: one")), s"the def should see the inductive: $out")

  test("an error is reported and the session continues"):
    // Brace-balanced, so the reader hands it over as one entry rather than reading
    // on looking for a closing brace.
    val out = session("this is not a declaration", "inductive Nat { case zero: Nat }")
    assert(out.exists(_.startsWith("Error:")), s"the bad input should be reported: $out")
    assert(out.exists(_.contains("inductive: Nat")), s"the session should continue: $out")
    assertEquals(out.last, "Goodbye.")

  // ---- the reader on its own ----

  test("readMultiLine keeps reading while braces are open"):
    val read = scripted("inductive Nat {", "  case zero: Nat", "}")
    val got  = Main.readMultiLine("> ", read)
    assertEquals(got.map(_.linesIterator.size), Some(3))

  test("readMultiLine reports end of input as None, not as an empty line"):
    assertEquals(Main.readMultiLine("> ", scripted()), None)
    assertEquals(Main.readMultiLine("> ", scripted("")), Some("\n"))
