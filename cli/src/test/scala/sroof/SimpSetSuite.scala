package sroof

import munit.FunSuite
import sroof.syntax.{Elaborator, Parser}

/** Tests for @[simp] attribute wiring: defspecs marked @[simp] should be
 *  automatically used by `simplify` (with no explicit lemma list).
 */
class SimpSetSuite extends FunSuite:

  private def check(src: String): Either[String, ?] =
    Main.processSource(src, "<SimpSetSuite>")

  // ---- @[simp] on def ----

  test("@[simp] def is added to simpSet"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      @[simp] def id(n: Nat): Nat { n }
    """
    assert(check(src).isRight, s"source should elaborate: ${check(src)}")

  // ---- @[simp] on defspec ----

  test("@[simp] defspec elaborates without error"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      @[simp] defspec plus_zero_left(m: Nat): plus(Nat.zero, m) = m {
        by trivial
      }
    """
    assert(check(src).isRight, s"@[simp] defspec should check: ${check(src)}")

  // ---- simplify queries simpSet ----

  test("simplify with no lemmas uses @[simp] defspec from simpSet"):
    // plus_zero_left is in simpSet; bar proves the same proposition using `by simplify`
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      @[simp] defspec plus_zero_left(m: Nat): plus(Nat.zero, m) = m {
        by trivial
      }
      defspec plus_zero_left_again(k: Nat): plus(Nat.zero, k) = k {
        by simplify
      }
    """
    assert(check(src).isRight, s"simplify should use simpSet lemma: ${check(src)}")

  test("simplify with no lemmas uses trivial when simpSet is empty"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_left(m: Nat): plus(Nat.zero, m) = m {
        by simplify
      }
    """
    assert(check(src).isRight, s"simplify with empty simpSet should fall back to trivial: ${check(src)}")

  test("simplify with no lemmas fails when goal is non-trivial and simpSet cannot help"):
    val src = """
      inductive Nat {
        case zero: Nat
        case succ(n: Nat): Nat
      }
      def plus(n: Nat, m: Nat): Nat {
        match n {
          case Nat.zero    => m
          case Nat.succ(k) => Nat.succ(plus(k, m))
        }
      }
      defspec plus_zero_right(n: Nat): plus(n, Nat.zero) = n {
        by simplify
      }
    """
    // plus(n, zero) = n is NOT trivial (requires induction), so simplify should fail
    assert(check(src).isLeft, "simplify should fail when goal is non-trivial and no simp lemmas can help")

  // ---- the default set must only hold names that resolve ----
  //
  // `Builtins.checkLemmaNames` reports a `simplify` lemma that resolves to
  // nothing, but only for names the *user wrote*. For the default set it is
  // skipped, and the recorded reason was that those names come from `@[simp]`
  // annotations "on definitions that exist by construction". That held for
  // `@[simp] def` and not for `@[simp] defspec`: the elaborator registered the
  // name immediately, while the definition is added by `Checker` only once the
  // proof is produced. So the default set carried a name that resolved to
  // nothing, and `simplify` with no lemmas degraded to `trivial` in silence.
  //
  // It also put an *unproved* — and, with `sorry`, an unsound — lemma in the set
  // that `simplify` consults implicitly, where sorry-taint tracking cannot see
  // it: taint is propagated from the lemma names a proof writes down, and this
  // one is never written down. `frontend.ModuleVerifier` states the opposite
  // discipline for the Scala path ("a theorem enters simpSet only after the
  // kernel has accepted its proof"); the two frontends now agree.

  private val source =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |@[simp] def double(n: Nat): Nat {
       |  match n {
       |    case Nat.zero    => Nat.zero
       |    case Nat.succ(k) => Nat.succ(Nat.succ(double(k)))
       |  }
       |}
       |@[simp] defspec double_zero(): double(Nat.zero) = Nat.zero {
       |  by trivial
       |}
       |""".stripMargin

  private def elaborated =
    Parser.parseProgram(source).flatMap(ds => Elaborator.elaborate(ds)) match
      case Right(r) => r
      case Left(e)  => fail(s"the fixture did not elaborate: $e")

  test("every name in the default simp set resolves to a definition"):
    // The invariant, stated directly. Before the fix `double_zero` was in the set
    // with no definition behind it.
    val r = elaborated
    val unresolved = r.env.simpSet.filter(n => r.env.lookupDef(n).isEmpty)
    assertEquals(unresolved, Set.empty[String],
      s"names in the default simp set that resolve to nothing: $unresolved")

  test("an @[simp] def is still registered at elaboration"):
    // The control: withholding *everything* would satisfy the first test and lose
    // the feature. A definition exists as soon as it is elaborated, so it belongs
    // in the set immediately.
    assert(elaborated.env.simpSet.contains("double"),
      "an @[simp] def should be in the default simp set")

  test("an @[simp] defspec is recorded, not discarded"):
    // Withheld from `env`, but not dropped: `Checker` adds it once the proof is
    // produced and un-tainted.
    assertEquals(elaborated.simpDefspecs, Set("double_zero"))

  test("the file still checks"):
    val js = Main.processSourceJson(source, "t.sroof")
    assert(js.contains("\"ok\":true"), s"the fixture stopped checking:\n$js")
