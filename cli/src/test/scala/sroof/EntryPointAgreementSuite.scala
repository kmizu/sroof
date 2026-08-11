package sroof

import munit.FunSuite
import sroof.core.GlobalEnv
import scala.collection.mutable.ListBuffer

/** Six ways into the same pipeline, and they have to agree.
  *
  * The pipeline is entered from `processSource`, `processSourceWithWarnings`,
  * `processSourceWithIncrementalStats` (the cached path, used by `sroof extract`),
  * `processSourceWithChecks`, `processSourceJson` (`--json`), and
  * `processDeclaration` (the REPL). Each one assembles the phases itself.
  *
  * That has now produced the same bug three times. `#check` was computed and
  * discarded in the file path (fixed in v0.15), then in the REPL (v0.22), then in
  * the cached path — where it meant `sroof extract` emitted code from a file
  * `sroof check` rejects. Fixing one entry point says nothing about the others, so
  * this suite asks all of them the same question and prints the disagreement.
  *
  * The accepting half matters as much: an entry point that rejected everything
  * would pass the rejecting half on its own.
  */
class EntryPointAgreementSuite extends FunSuite:

  private val prelude =
    """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
       |inductive Bool { case tru: Bool  case fls: Bool }
       |""".stripMargin

  /** Every entry point, as a predicate: did it reject this source? */
  private val entryPoints: List[(String, String => Boolean)] = List(
    "processSource"        -> (s => Main.processSource(s, "t.sroof").isLeft),
    "withWarnings"         -> (s => Main.processSourceWithWarnings(s, "t.sroof").isLeft),
    "withIncrementalStats" -> (s => Main.processSourceWithIncrementalStats(s, "t.sroof").isLeft),
    "withChecks"           -> (s => Main.processSourceWithChecks(s, "t.sroof").isLeft),
    "json"                 -> (s =>
      Main.processSourceJson(s, "t.sroof").startsWith("""{"schemaVersion":2,"ok":false""")),
    "repl"                 -> (s => replRejects(s)),
  )

  /** Feed a source to the REPL a line at a time; did it report an error? */
  private def replRejects(source: String): Boolean =
    val out  = ListBuffer.empty[String]
    val it   = source.linesIterator
    var past = 0
    given GlobalEnv = GlobalEnv.empty
    Main.runRepl(
      _ =>
        if it.hasNext then it.next()
        else
          past += 1
          if past > 200 then fail("the REPL kept reading after end of input")
          null,
      out += _,
    )
    out.exists(_.startsWith("Error:"))

  private val mustReject: List[(String, String)] = List(
    "a parse error"                -> "inductive {{{ oops",
    "an unknown name"              -> (prelude + "def f(): Nat { nosuchthing }\n"),
    "a false theorem"              -> (prelude + "defspec f: Nat.zero = Nat.succ(Nat.zero) { by trivial }\n"),
    "a def body of the wrong type" -> (prelude + "def f(): Nat { Bool.tru }\n"),
    "an ill-typed #check"          -> (prelude + "#check Nat.succ(Bool.tru)\n"),
    "a #check on an unknown name"  -> (prelude + "#check nosuchthing\n"),
  )

  private val mustAccept: List[(String, String)] = List(
    "an inductive alone"     -> prelude,
    "a def and a theorem"    -> (prelude +
      """|def plus(a: Nat, b: Nat): Nat {
         |  match a { case Nat.zero => b  case Nat.succ(k) => Nat.succ(plus(k, b)) }
         |}
         |defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
         |  by induction n { case zero => trivial  case succ k ih => simplify [ih] }
         |}
         |""".stripMargin),
    "a well-typed #check"    -> (prelude + "#check Nat.succ(Nat.zero)\n"),
    // `sorry` is a warning, not an error, unless --fail-on-sorry is given. Every
    // entry point has to agree about that too — including the ones that cannot be
    // given the flag.
    "a sorry"                -> (prelude + "defspec s: Nat.zero = Nat.zero { by sorry }\n"),
  )

  private def disagreements(cases: List[(String, String)], expected: Boolean): List[String] =
    cases.flatMap { (label, src) =>
      val verdicts = entryPoints.map((name, run) => name -> run(src))
      val wrong    = verdicts.filter(_._2 != expected).map(_._1)
      if wrong.isEmpty then None
      else
        val want = if expected then "reject" else "accept"
        Some(s"$label: expected every entry point to $want it; these did not: ${wrong.mkString(", ")}")
    }

  test("every entry point rejects what any of them rejects"):
    val bad = disagreements(mustReject, expected = true)
    assert(bad.isEmpty, bad.mkString("\n"))

  test("every entry point accepts what any of them accepts"):
    val bad = disagreements(mustAccept, expected = false)
    assert(bad.isEmpty, bad.mkString("\n"))
