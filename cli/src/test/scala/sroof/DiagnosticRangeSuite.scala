package sroof

import munit.FunSuite

/** Where a diagnostic says the error is.
  *
  * `rangeFor` ended in `fallbackRange`, which returned the first non-whitespace
  * character of the file. So an error anywhere was reported at the first
  * declaration — an editor underlined innocent code with complete confidence, and
  * the further down the file the real error was, the more wrong it looked.
  *
  * Nothing tested this: the two existing assertions check that the `range` *key* is
  * present, which it is even when the value is `null`.
  */
class DiagnosticRangeSuite extends FunSuite:

  // A blank first line, so a range that has merely defaulted to the top of the file
  // is visibly different from one that found the error.
  private val prelude =
    "\ninductive Nat { case zero: Nat  case succ(n: Nat): Nat }\ninductive Bool { case tru: Bool }\n"

  private def rangeOf(bad: String): Option[(Int, Int)] =
    val js = Main.processSourceJson(prelude + bad, "t.sroof")
    """"range":\{"start":\{"line":(\d+),"column":(\d+)\}""".r
      .findFirstMatchIn(js)
      .map(m => (m.group(1).toInt, m.group(2).toInt))

  test("an unknown name is reported where it is written"):
    // Line 4 is `def f(): Nat { nosuchthing }`; the name starts at column 16.
    val r = rangeOf("def f(): Nat { nosuchthing }\n")
    assertEquals(r.map(_._1), Some(4), s"expected line 4, got $r")
    assertEquals(r.map(_._2), Some(16), s"expected the column of the name, got $r")

  test("a failing proof is reported on its defspec"):
    val r = rangeOf("defspec f: Nat.zero = Nat.succ(Nat.zero) { by trivial }\n")
    assertEquals(r.map(_._1), Some(4), s"expected line 4, got $r")

  test("a range is omitted rather than guessed"):
    // A `#check` failure has no location to offer, and says so. Reporting line 1
    // would be a confident answer to a question the producer cannot answer.
    val js = Main.processSourceJson(prelude + "#check Nat.succ(Bool.tru)\n", "t.sroof")
    assert(js.contains("\"range\":null"), s"expected a null range, got:\n$js")

  test("the error is not attributed to the first declaration"):
    // The property the fallback broke, stated directly: two files differing only in
    // where the bad line sits must not produce the same range.
    val early = rangeOf("def f(): Nat { nosuchthing }\n")
    val late  = rangeOf("def g(): Nat { Nat.zero }\ndef f(): Nat { nosuchthing }\n")
    assert(early != late, s"the range did not move with the error: $early vs $late")
