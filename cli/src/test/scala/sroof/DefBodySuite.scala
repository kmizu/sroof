package sroof

import munit.FunSuite
import java.nio.file.{Files, Paths}

/** `def` bodies are checked against their declared types.
  *
  * Until v0.14 they were not. Only a `defspec` reached the kernel, so a definition
  * could say one thing and mean another — and every proposition is written in terms
  * of definitions. Each `HOLE` case below was accepted on the v0.13 tree.
  */
class DefBodySuite extends FunSuite:

  private val nat =
    """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
       |inductive Bool { case tru: Bool  case fls: Bool }
       |""".stripMargin

  private def check(src: String) = Main.processSource(nat + src, "def.sroof")

  private def assertTypeError(src: String, clue: String): Unit =
    val r = check(src)
    assert(r.isLeft, s"$clue — expected rejection, got: $r")
    val msg = r.swap.toOption.get
    assert(
      msg.contains("does not match its declared type"),
      s"$clue — rejected, but not as a definition/type mismatch. A parse error is " +
        s"also a Left and would make this test vacuous. Message was: $msg",
    )

  test("HOLE: a body of the wrong type is rejected"):
    assertTypeError("def f(n: Nat): Nat { Bool.tru }", "a Bool body under a Nat signature")

  test("HOLE: a parameter used at the wrong type is rejected"):
    assertTypeError("def fake(b: Bool): Nat { b }", "a Bool returned as a Nat")

  test("HOLE: a wrong recursive call is rejected"):
    assertTypeError(
      """|def g(n: Nat): Nat {
         |  match n {
         |    case Nat.zero    => Nat.zero
         |    case Nat.succ(k) => Bool.tru
         |  }
         |}
         |""".stripMargin,
      "one branch returning a Bool",
    )

  test("a correct definition is still accepted"):
    // The control. Without it, a change that rejected every definition would pass
    // every test above.
    val r = check(
      """|def plus(a: Nat, b: Nat): Nat {
         |  match a {
         |    case Nat.zero    => b
         |    case Nat.succ(k) => Nat.succ(plus(k, b))
         |  }
         |}
         |defspec plus_zero(b: Nat): plus(Nat.zero, b) = b { by trivial }
         |""".stripMargin
    )
    assert(r.isRight, s"expected acceptance, got: $r")

  test("a dependent return index is verified"):
    // The reason this matters beyond hygiene: `vapp` declares that appending an
    // n-vector to an m-vector yields a `plus(n, m)`-vector. That is the theorem,
    // and there is no separate lemma to prove — so if the body is unchecked, the
    // claim is a comment.
    val vec =
      """|inductive Vec(A: Type)(n: Nat) {
         |  case vnil: Vec(A)(Nat.zero)
         |  case vcons(m: Nat, head: A, tail: Vec(A)(m)): Vec(A)(Nat.succ(m))
         |}
         |def plus(a: Nat, b: Nat): Nat {
         |  match a {
         |    case Nat.zero    => b
         |    case Nat.succ(k) => Nat.succ(plus(k, b))
         |  }
         |}
         |""".stripMargin
    val body =
      """|def vapp(A: Type, n: Nat, m: Nat, xs: Vec(A)(n), ys: Vec(A)(m)): Vec(A)(RET) {
         |  match xs {
         |    case Vec.vnil           => ys
         |    case Vec.vcons(k, h, t) => Vec.vcons(plus(k, m), h, vapp(A, k, m, t, ys))
         |  }
         |}
         |""".stripMargin
    val good = check(vec + body.replace("RET", "plus(n, m)"))
    assert(good.isRight, s"the honest length must be accepted, got: $good")
    assertTypeError(vec + body.replace("RET", "Nat.zero"), "a vapp claiming length zero")

  test("HOLE: an evaluator failure is a diagnostic, never a crash"):
    // `def fake(b: Bool): Nat { b }` used as a match scrutinee made `Eval` throw
    // `Non-exhaustive match: no case for constructor 'tru'`, which escaped the CLI
    // as a stack trace. The same shape reached users through nothing more exotic
    // than passing arguments in the wrong order.
    val r = check(
      """|def fake(b: Bool): Nat { b }
         |def useit(b: Bool): Nat {
         |  match fake(b) {
         |    case Nat.zero    => Nat.zero
         |    case Nat.succ(k) => k
         |  }
         |}
         |defspec t: useit(Bool.tru) = Nat.zero { by trivial }
         |""".stripMargin
    )
    assert(r.isLeft, s"expected rejection, got: $r")

  test("every shipped .sroof file has type-correct definitions"):
    // Finding this hole turned up five real defects: `stdlib/PolyList.sroof`'s three
    // polymorphic functions and both `concat`s declared their type parameter last,
    // which forces a bare `PolyList`/`Vec` in the signature where the value has the
    // applied type — the anti-pattern PolyList's own header warns against.
    val files = (
      Option(Paths.get("stdlib").toFile.listFiles).toList.flatten ++
        Option(Paths.get("examples").toFile.listFiles).toList.flatten
    ).filter(_.getName.endsWith(".sroof")).map(_.getPath).sorted
    assert(files.length > 20, s"expected the shipped corpus, found ${files.length} files")
    val failures = files.flatMap { f =>
      val src = Files.readString(Paths.get(f))
      Main.processSource(src, f) match
        case Left(e) if e.contains("does not match its declared type") => Some(s"$f: $e")
        case _                                                         => None
    }
    assert(failures.isEmpty, s"definitions that do not check:\n${failures.mkString("\n")}")
