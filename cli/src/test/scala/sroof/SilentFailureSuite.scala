package sroof

import munit.FunSuite

/** Failures that used to be swallowed.
  *
  * Each case here was reported as `OK` — or as an error about something else — on
  * the v0.14 tree. None of them was unsound: the kernel still had the final say.
  * They were worse in a different way, sending you to debug the wrong thing.
  */
class SilentFailureSuite extends FunSuite:

  private val prelude =
    """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
       |inductive Bool { case tru: Bool  case fls: Bool }
       |""".stripMargin

  // ---- #check ----

  test("a #check that does not type-check fails the file"):
    // Previously the error string was computed, the plain CLI never printed it,
    // and the file reported OK. A `#check` is an assertion the author wrote.
    val r = Main.processSourceWithChecks(prelude + "#check Nat.succ(Bool.tru)\n", "t.sroof")
    assert(r.isLeft, s"an ill-typed #check must fail the file, got: $r")
    assert(
      r.swap.toOption.get.contains("#check"),
      s"the message must name #check, got: ${r.swap.toOption.get}",
    )

  test("a #check on an unknown name fails the file"):
    val r = Main.processSourceWithChecks(prelude + "#check unknownThing\n", "t.sroof")
    assert(r.isLeft, s"expected rejection, got: $r")

  test("a well-typed #check still reports its type"):
    // The control: a change that rejected every #check would pass the two above.
    val r = Main.processSourceWithChecks(prelude + "#check Nat.succ(Nat.zero)\n", "t.sroof")
    assert(r.isRight, s"expected acceptance, got: $r")
    val (_, _, checks) = r.toOption.get
    assertEquals(checks.length, 1)
    assert(checks.head._2.contains("Nat"), s"type should be Nat, got: ${checks.head._2}")

  test("JSON agrees with the plain path about a bad #check"):
    // The JSON path had its own copy of the logic: it flagged the individual check
    // as ok:false while the document still said ok:true, so tooling and the CLI
    // exit code disagreed about the same file.
    // Match the *top-level* flag by its position in the document: `contains` alone
    // would be satisfied by the per-check `"ok":false` inside the checks array, and
    // the test would pass on the very tree it is meant to reject.
    val json = Main.processSourceJson(prelude + "#check Nat.succ(Bool.tru)\n", "t.sroof")
    assert(
      json.startsWith("""{"schemaVersion":2,"ok":false"""),
      s"top-level ok must be false: $json",
    )
    assert(json.contains("\"phase\":\"check\""), s"phase must be check: $json")
    val good = Main.processSourceJson(prelude + "#check Nat.zero\n", "t.sroof")
    assert(
      good.startsWith("""{"schemaVersion":2,"ok":true"""),
      s"a good #check must stay ok: $good",
    )

  // ---- simplify ----

  test("simplify names an unknown lemma instead of ignoring it"):
    // `tryGlobalLemmaAsIH` fell back to `trivial`, so a typo was silent whenever the
    // goal closed anyway.
    val r = Main.processSource(
      prelude + "defspec t(n: Nat): n = n { by simplify [no_such_lemma] }\n", "t.sroof")
    assert(r.isLeft, s"expected rejection, got: $r")
    assert(
      r.swap.toOption.get.contains("unknown lemma 'no_such_lemma'"),
      s"the message must name the lemma, got: ${r.swap.toOption.get}",
    )

  test("simplify names a mistyped hypothesis rather than blaming the goal"):
    // The worse half: on a goal `trivial` cannot close, the error used to point at
    // the goal, so you debugged the proof instead of the spelling.
    val r = Main.processSource(
      """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
         |def plus(a: Nat, b: Nat): Nat {
         |  match a {
         |    case Nat.zero    => b
         |    case Nat.succ(k) => Nat.succ(plus(k, b))
         |  }
         |}
         |defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
         |  by induction n {
         |    case zero      => trivial
         |    case succ k ih => simplify [ih_typo]
         |  }
         |}
         |""".stripMargin,
      "t.sroof",
    )
    assert(r.isLeft, s"expected rejection, got: $r")
    assert(
      r.swap.toOption.get.contains("unknown lemma 'ih_typo'"),
      s"the message must name the typo, got: ${r.swap.toOption.get}",
    )

  test("a real hypothesis and a real lemma are still accepted"):
    // The control for both simplify cases.
    val r = Main.processSource(
      """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
         |def plus(a: Nat, b: Nat): Nat {
         |  match a {
         |    case Nat.zero    => b
         |    case Nat.succ(k) => Nat.succ(plus(k, b))
         |  }
         |}
         |defspec plus_zero(n: Nat): plus(n, Nat.zero) = n {
         |  by induction n {
         |    case zero      => trivial
         |    case succ k ih => simplify [ih]
         |  }
         |}
         |""".stripMargin,
      "t.sroof",
    )
    assert(r.isRight, s"expected acceptance, got: $r")
