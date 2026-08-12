package sroof

import munit.FunSuite

/** What the tool says when the *statement* is wrong, not the proof.
  *
  * An ill-typed statement was never accepted — `executeProof` catches the
  * evaluator exception it causes — but it was reported as
  * "Internal error while running the proof: Non-exhaustive match: no case for
  * constructor 'tru'. This is a bug in sroof", which blames the tool for
  * something the author wrote, and pointed the range at the first textual match
  * of `tru` elsewhere in the file. The author has no way to act on that.
  *
  * The blind spot underneath: `Bidirectional.inferUniverse` answers `Right(0)`
  * for an applied `Eq` **without inspecting the arguments**, so the shape alone
  * counted as evidence that the statement was a proposition.
  */
class StatementSuite extends FunSuite:

  private val prelude =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |inductive Bool {
       |  case tru: Bool
       |  case fls: Bool
       |}
       |def plus(n: Nat, m: Nat): Nat {
       |  match n {
       |    case Nat.zero    => m
       |    case Nat.succ(k) => Nat.succ(plus(k, m))
       |  }
       |}
       |""".stripMargin

  /** `plus` matches on a `Nat`, so `plus(Bool.tru, …)` is a term of no type. It
    * is reflexively equal to itself, which is why `trivial` reaches it at all.
    */
  private val illTyped =
    "defspec bad: plus(Bool.tru, Nat.zero) = plus(Bool.tru, Nat.zero) { by trivial }\n"

  private def json(src: String) = Main.processSourceJson(prelude + src, "t.sroof")

  test("an ill-typed statement is not reported as a bug in sroof"):
    val js = json(illTyped)
    assert(js.contains("\"ok\":false"), s"expected a failure, got:\n$js")
    assert(!js.contains("This is a bug in sroof"),
      s"a statement the author wrote was reported as a defect in the tool:\n$js")

  test("an ill-typed statement is named as a malformed statement"):
    val js = json(illTyped)
    assert(js.contains("is not a proposition"),
      s"the failure does not say what is wrong with it:\n$js")

  test("the range points at the declaration, not at a term elsewhere"):
    // This one passes on the previous tree too, and is here for the opposite
    // reason: the old message happened to match `DefspecFailurePattern`, so
    // introducing a new wording silently moved the range to line 6, the first
    // textual `tru`. Every message that names a defspec has to be in that
    // pattern; this is what says so.
    val js = json(illTyped)
    val line = """"range":\{"start":\{"line":(\d+)""".r
      .findFirstMatchIn(js).map(_.group(1).toInt)
    assertEquals(line, Some(15), s"expected the defspec line, got $line in:\n$js")

  test("a well-formed statement is still proved"):
    val js = json("defspec good: plus(Nat.zero, Nat.zero) = Nat.zero { by trivial }\n")
    assert(js.contains("\"ok\":true"), s"a well-formed defspec was rejected:\n$js")
