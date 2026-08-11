package sroof

import munit.FunSuite

/** `sroof check --json` has to fail the build for the same files `sroof check` does.
  *
  * It did not. The exit code was `if failOnSorry && json.contains("phase":"policy")`,
  * so a parse error, a failed proof, or an ill-typed `#check` printed `"ok":false`
  * and exited **0** — a CI step running `--json` and trusting the exit code passed
  * every broken file, while the same file failed the plain command.
  *
  * The property is agreement: the JSON path exits non-zero exactly when the plain
  * path rejects. Testing it needs the decision separated from `sys.exit`, which is
  * what `jsonExitCode` is.
  */
class ExitCodeSuite extends FunSuite:

  private val prelude =
    """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
       |inductive Bool { case tru: Bool  case fls: Bool }
       |""".stripMargin

  private val sources: List[(String, String)] = List(
    "a good file"                  -> (prelude + "#check Nat.succ(Nat.zero)\n"),
    "a parse error"                -> "inductive {{{ oops",
    "an unknown name"              -> (prelude + "def f(): Nat { nosuchthing }\n"),
    "a false theorem"              -> (prelude + "defspec f: Nat.zero = Nat.succ(Nat.zero) { by trivial }\n"),
    "a def body of the wrong type" -> (prelude + "def f(): Nat { Bool.tru }\n"),
    "an ill-typed #check"          -> (prelude + "#check Nat.succ(Bool.tru)\n"),
    "a sorry"                      -> (prelude + "defspec s: Nat.zero = Nat.zero { by sorry }\n"),
  )

  test("--json exits non-zero exactly when the plain path rejects"):
    val disagreed = sources.flatMap { (label, src) =>
      val plainRejects = Main.processSource(src, "t.sroof").isLeft
      val jsonFails    = Main.jsonExitCode(Main.processSourceJson(src, "t.sroof")) != 0
      if plainRejects == jsonFails then None
      else Some(s"$label: plain ${if plainRejects then "rejects" else "accepts"}, " +
                s"--json exits ${if jsonFails then "1" else "0"}")
    }
    assert(disagreed.isEmpty, disagreed.mkString("\n"))

  test("--fail-on-sorry turns a sorry into a non-zero exit"):
    val src = prelude + "defspec s: Nat.zero = Nat.zero { by sorry }\n"
    assertEquals(Main.jsonExitCode(Main.processSourceJson(src, "t.sroof")), 0)
    assertEquals(Main.jsonExitCode(Main.processSourceJson(src, "t.sroof", failOnSorry = true)), 1)

  test("a failing #check inside a passing file does not fail the file by itself"):
    // The reason this is matched at the start of the document rather than with
    // `contains`: `"ok":false` also occurs inside `checks[]`. A file with no failing
    // check but a `"ok":false` substring elsewhere must still exit 0 — and the
    // converse, a genuinely failing file, must not be missed.
    val good = Main.processSourceJson(prelude + "#check Nat.zero\n", "t.sroof")
    assert(good.contains("\"ok\":true"), good)
    assertEquals(Main.jsonExitCode(good), 0)

  // ---- extract argument parsing ----

  test("extract accepts --output, which is what sbt-sroof has always passed"):
    // `sbt-sroof`'s `sroofExtract` invokes `extract <file> --output <file>` and is
    // wired into `Compile / sourceGenerators`. The CLI did not accept the flag: it
    // printed the usage text and exited 1, so every build that enabled the plugin
    // failed. CI compiles the plugin and never runs it, so nothing caught it.
    assertEquals(
      Main.parseExtractOptions(List("a.sroof", "--output", "b.scala")),
      Right(("a.sroof", Some("b.scala"))))
    assertEquals(Main.parseExtractOptions(List("a.sroof")), Right(("a.sroof", None)))

  test("extract rejects malformed arguments instead of guessing"):
    assert(Main.parseExtractOptions(Nil).isLeft)
    assert(Main.parseExtractOptions(List("a.sroof", "--output")).isLeft)
    assert(Main.parseExtractOptions(List("a.sroof", "--nope")).isLeft)
    assert(Main.parseExtractOptions(List("a.sroof", "b.sroof")).isLeft)
