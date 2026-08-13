package sroof

import munit.FunSuite

/** The second file that proved `0 = 1` — no arrow at the occurrence, no
  * recursion at the term level.
  *
  * v0.35 recorded the positivity hole as unreachable because the `.sroof`
  * grammar will not put a function type inside a type application. That was the
  * wrong conclusion from the right observation: the parser only blocks the
  * arrow's *direct* spelling. Wrap the negativity in another inductive —
  * `Neg(A) { mk(f: A -> Empty) }` — and `Neg(Bad)` smuggles it through with no
  * arrow in sight. Measured on the previous tree: the file below printed
  * `OK … 1 defspec(s)` and exited 0.
  *
  * The termination checker is *correctly* silent here: `notBad` makes no
  * recursive call. The recursion rides in the data — which is precisely the
  * thing strict positivity exists to forbid.
  */
class PositivityGateSuite extends FunSuite:

  private val prelude =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |inductive Empty {
       |}
       |inductive Neg(A: Type) {
       |  case mk(f: A -> Empty): Neg(A)
       |}
       |""".stripMargin

  private def json(src: String) = Main.processSourceJson(prelude + src, "t.sroof")

  test("the declaration alone is rejected"):
    val js = json(
      """|inductive Bad {
         |  case mk(w: Neg(Bad)): Bad
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":false"),
      s"a negative occurrence through Neg's parameter was accepted:\n$js")
    assert(js.contains("Strict positivity violation"),
      s"rejected, but not by the positivity gate:\n$js")

  test("the full file that proved 0 = 1 is rejected"):
    val js = json(
      """|inductive Bad {
         |  case mk(w: Neg(Bad)): Bad
         |}
         |def notBad(b: Bad): Empty {
         |  match b {
         |    case Bad.mk(w) =>
         |      match w {
         |        case Neg.mk(f) => f(b)
         |      }
         |  }
         |}
         |def bad(u: Nat): Bad {
         |  Bad.mk(Neg.mk(notBad))
         |}
         |def falseVal(u: Nat): Empty {
         |  notBad(bad(u))
         |}
         |defspec zero_is_one: Nat.zero = Nat.succ(Nat.zero) {
         |  by exact match falseVal(Nat.zero) { }
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":false"), s"a proof of 0 = 1 was accepted:\n$js")
    assert(js.contains("Strict positivity violation"),
      s"rejected, but not at the declaration that enables it:\n$js")

  test("nesting through a positive parameter still checks"):
    // The control: `Wrap` uses its parameter strictly positively, so rose-tree
    // style nesting is legitimate and provable things about it must survive.
    val js = json(
      """|inductive Wrap(A: Type) {
         |  case wrap(a: A): Wrap(A)
         |}
         |inductive Tree {
         |  case leaf: Tree
         |  case node(w: Wrap(Tree)): Tree
         |}
         |def one(t: Tree): Nat {
         |  match t {
         |    case Tree.leaf    => Nat.zero
         |    case Tree.node(w) => Nat.succ(Nat.zero)
         |  }
         |}
         |defspec one_leaf: one(Tree.leaf) = Nat.zero {
         |  by trivial
         |}
         |""".stripMargin)
    assert(js.contains("\"ok\":true"), s"benign nesting was rejected:\n$js")
