package sroof

import munit.FunSuite
import java.nio.file.{Files, Paths}

/** `docs/json-schema.md` is a contract, so it is tested like one.
  *
  * Nothing checked it before, and the producer had drifted from it in three ways:
  * `result` was an object alongside `"ok":false` for the two failures that happen
  * late (a bad `#check`, and `--fail-on-sorry`), so a consumer testing
  * `result === null` for failure got the wrong answer; a `#check` type error was
  * reported as `"phase":"policy"` because the branch reused the nearest diagnostic
  * helper, contradicting the `"phase":"check"` in the same response; and the
  * document listed neither the `policy` phase nor the `sorryDiagnostics` field the
  * producer had been emitting.
  *
  * The last case here is the drift guard: every phase and code the producer can emit
  * has to appear in the document.
  */
class JsonSchemaContractSuite extends FunSuite:

  private val prelude =
    """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
       |inductive Bool { case tru: Bool  case fls: Bool }
       |""".stripMargin

  /** (label, source, failOnSorry) covering every phase the producer can report. */
  private val cases: List[(String, String, Boolean)] = List(
    ("success",        prelude + "#check Nat.succ(Nat.zero)\n",                          false),
    ("success + sorry", prelude + "defspec s: Nat.zero = Nat.zero { by sorry }\n",        false),
    ("parse",          "inductive {{{ oops",                                              false),
    ("elab",           prelude + "def f(): Nat { nosuchthing }\n",                        false),
    ("proof",          prelude + "defspec f: Nat.zero = Nat.succ(Nat.zero) { by trivial }\n", false),
    ("check",          prelude + "#check Nat.succ(Bool.tru)\n",                           false),
    ("policy",         prelude + "defspec s: Nat.zero = Nat.zero { by sorry }\n",         true),
  )

  private def json(src: String, failOnSorry: Boolean): String =
    Main.processSourceJson(src, "t.sroof", failOnSorry = failOnSorry)

  /** First value of a top-level scalar field. The top-level object is emitted before
    * any nested one, so the first occurrence is the one wanted.
    */
  private def topLevel(js: String, name: String): String =
    val pat = ("\"" + name + "\":(null|true|false|\\d+|\\{|\"(?:[^\"\\\\]|\\\\.)*\")").r
    pat.findFirstMatchIn(js).map(_.group(1)).getOrElse(fail(s"no field '$name' in: $js"))

  /** Every `"phase":"…"` in the document, top-level first, diagnostics after. */
  private def phases(js: String): List[String] =
    "\"phase\":\"([a-z_]+)\"".r.findAllMatchIn(js).map(_.group(1)).toList

  private def codes(js: String): List[String] =
    "\"code\":\"([a-z_]+)\"".r.findAllMatchIn(js).map(_.group(1)).toList

  private def diagnosticCount(js: String): Int =
    "\"diagnostics\":\\[(.*?)\\],\"checks\"".r.findFirstMatchIn(js)
      .map(m => if m.group(1).isEmpty then 0 else m.group(1).count(_ == '{')).getOrElse(-1)

  test("schemaVersion is 2 in every response"):
    cases.foreach((label, src, f) => assertEquals(topLevel(json(src, f), "schemaVersion"), "2", label))

  test("result is null exactly when ok is false"):
    cases.foreach { (label, src, f) =>
      val js = json(src, f)
      val ok = topLevel(js, "ok")
      val res = topLevel(js, "result")
      if ok == "false" then assertEquals(res, "null", s"$label: a failure must not carry a result")
      else assertEquals(res, "{", s"$label: a success must carry a result")
    }

  test("error is a string exactly when ok is false"):
    cases.foreach { (label, src, f) =>
      val js = json(src, f)
      val isErr = topLevel(js, "error") != "null"
      assertEquals(isErr, topLevel(js, "ok") == "false", s"$label: error must track ok")
    }

  test("a failure carries at least one diagnostic and a success carries none"):
    cases.foreach { (label, src, f) =>
      val js = json(src, f)
      val n  = diagnosticCount(js)
      if topLevel(js, "ok") == "false" then assert(n >= 1, s"$label: expected a diagnostic, got $n")
      else assertEquals(n, 0, s"$label: a success must not carry diagnostics")
    }

  test("every diagnostic agrees with the top-level phase"):
    // One response disagreeing with itself is worse than either answer: a consumer
    // routing on the diagnostic phase and one routing on the top-level phase would
    // classify the same failure differently.
    cases.foreach { (label, src, f) =>
      val all = phases(json(src, f))
      assert(all.nonEmpty, s"$label: no phase at all")
      assert(all.distinct.sizeIs == 1, s"$label: mixed phases ${all.distinct}")
    }

  test("the document lists every phase and code the producer emits"):
    val doc = Files.readString(Paths.get("docs/json-schema.md"))
    val emittedPhases = cases.flatMap((_, src, f) => phases(json(src, f))).distinct.sorted
    val emittedCodes  = cases.flatMap((_, src, f) => codes(json(src, f))).distinct.sorted
    val missingPhases = emittedPhases.filterNot(p => doc.contains(s""""$p"""))
    val missingCodes  = emittedCodes.filterNot(c => doc.contains(s""""$c""""))
    assert(missingPhases.isEmpty, s"phases emitted but undocumented: $missingPhases")
    assert(missingCodes.isEmpty,  s"codes emitted but undocumented: $missingCodes")
    // And the fields, which is how `sorryDiagnostics` went unmentioned for so long.
    val fields = List(
      "schemaVersion", "ok", "phase", "file", "result",
      "warnings", "sorryDiagnostics", "diagnostics", "checks", "error",
    )
    val missingFields = fields.filterNot(doc.contains)
    assert(missingFields.isEmpty, s"fields emitted but undocumented: $missingFields")
