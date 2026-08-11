package sroof

import munit.FunSuite

class IncrementalSuite extends FunSuite:

  private val baseSource =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |defspec refl(n: Nat): n = n {
       |  by trivial
       |}
       |""".stripMargin

  test("no-change re-run hits parse/elab/proof caches") {
    Main.resetIncrementalCache()

    val first = Main.processSourceWithIncrementalStats(baseSource, "inc-nochange.sroof")
    assert(first.isRight, s"first run should succeed: $first")
    val firstStats = first.toOption.get._4
    assert(!firstStats.parseCacheHit, s"first parse should miss cache: $firstStats")
    assert(!firstStats.elabCacheHit, s"first elab should miss cache: $firstStats")
    assert(!firstStats.proofCacheHit, s"first proof should miss cache: $firstStats")

    val second = Main.processSourceWithIncrementalStats(baseSource, "inc-nochange.sroof")
    assert(second.isRight, s"second run should succeed: $second")
    val secondStats = second.toOption.get._4
    assert(secondStats.parseCacheHit, s"second parse should hit cache: $secondStats")
    assert(secondStats.elabCacheHit, s"second elab should hit cache: $secondStats")
    assert(secondStats.proofCacheHit, s"second proof should hit cache: $secondStats")
  }

  test("non-semantic edit reuses downstream caches") {
    Main.resetIncrementalCache()

    val src1 = baseSource
    val src2 =
      """|// added comment
         |inductive Nat {
         |  case zero: Nat
         |  case succ(n: Nat): Nat
         |}
         |defspec refl(n: Nat): n = n {
         |  by trivial
         |}
         |""".stripMargin

    val first = Main.processSourceWithIncrementalStats(src1, "inc-comment.sroof")
    assert(first.isRight, s"first run should succeed: $first")

    val second = Main.processSourceWithIncrementalStats(src2, "inc-comment.sroof")
    assert(second.isRight, s"second run should succeed: $second")
    val stats = second.toOption.get._4
    assert(!stats.parseCacheHit, s"source changed so parse cache should miss: $stats")
    assert(stats.elabCacheHit, s"decl-level cache should allow elab reuse: $stats")
    assert(stats.proofCacheHit, s"program-level cache should allow proof reuse: $stats")
  }

  test("declaration change invalidates downstream cache and preserves correctness") {
    Main.resetIncrementalCache()

    val srcOk = baseSource
    val srcBad =
      """|inductive Nat {
         |  case zero: Nat
         |  case succ(n: Nat): Nat
         |}
         |defspec refl(n: Nat): n = Nat.zero {
         |  by trivial
         |}
         |""".stripMargin

    val first = Main.processSourceWithIncrementalStats(srcOk, "inc-invalid.sroof")
    assert(first.isRight, s"first run should succeed: $first")

    val second = Main.processSourceWithIncrementalStats(srcBad, "inc-invalid.sroof")
    assert(second.isLeft, s"changed declaration should fail and not reuse stale success: $second")
    val message = second.left.toOption.get
    assert(message.contains("Proof of 'refl' failed"), s"should report real proof failure:\n$message")
  }

  // ---- the program hash must mention everything that changes the outcome ----

  test("a constructor's return index changes the program hash"):
    // The surface-AST hash upstream already catches this, so the assertion is on
    // `programHashFor` doing its own job: it reads as the invalidation key, and an
    // input it omits is a landmine for whoever relies on it next.
    def src(nilIndex: String) =
      s"""|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
          |inductive Vec(A: Type)(n: Nat) {
          |  case vnil: Vec(A)($nilIndex)
          |  case vcons(m: Nat, head: A, tail: Vec(A)(m)): Vec(A)(Nat.succ(m))
          |}
          |defspec t: Vec(Nat)(Nat.zero) { Vec.vnil }
          |""".stripMargin
    Main.resetIncrementalCache()
    val first  = Main.processSourceWithIncrementalStats(src("Nat.zero"), "idx.sroof")
    assert(first.isRight, s"the length-zero version must check: $first")
    // `vnil` is now length one, so the defspec is false and must be rejected —
    // a cached "OK" surviving this would be the whole hazard.
    val second = Main.processSourceWithIncrementalStats(src("Nat.succ(Nat.zero)"), "idx.sroof")
    assert(second.isLeft, s"the changed index must be re-checked and rejected: $second")

  test("a definition's declared type changes the program hash"):
    def src(ret: String) =
      s"""|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
          |inductive Bool { case tru: Bool  case fls: Bool }
          |def f(n: Nat): $ret { n }
          |defspec t(n: Nat): n = n { by trivial }
          |""".stripMargin
    Main.resetIncrementalCache()
    assert(Main.processSourceWithIncrementalStats(src("Nat"), "dt.sroof").isRight)
    assert(
      Main.processSourceWithIncrementalStats(src("Bool"), "dt.sroof").isLeft,
      "changing the declared type must be re-checked and rejected",
    )
