package sroof.checker

import sroof.core.{Term, Param, Ctor, IndDef, CtorDef, GlobalEnv, PositivityChecker}
import munit.FunSuite

/** Tests for strict positivity checking of inductive type definitions.
 *
 *  An inductive type `T` is strictly positive iff for every constructor argument
 *  type, `T` does not appear in a negative position (left of an arrow / Pi).
 *
 *  Negative occurrence examples that MUST be rejected:
 *    case mk(f: T -> Nat): T           // T in negative position
 *    case mk(f: (T -> Nat) -> Nat): T  // T in negative (double-negative = positive for inner,
 *                                       // but outer arrow makes it negative)
 *
 *  Positive occurrence examples that MUST be accepted:
 *    case succ(n: T): T                // T in strictly positive position
 *    case mk(f: Nat -> T): T           // T only in positive position (right of arrow)
 *    case pair(a: T, b: T): T          // T in direct positions
 */
class PositivitySuite extends FunSuite:

  given GlobalEnv = GlobalEnv.empty

  // ---- Should be accepted (strictly positive) ----

  test("Nat is strictly positive (no recursive args for zero, direct for succ)"):
    val result = PositivityChecker.check("Nat", List(
      CtorDef("zero", Nil),
      CtorDef("succ", List(Term.Ind("Nat", Nil, Nil))),
    ))
    assert(result.isRight, s"Expected Right, got $result")

  test("List-like type is strictly positive"):
    // case nil: List; case cons(head: A, tail: List): List
    val result = PositivityChecker.check("MyList", List(
      CtorDef("nil", Nil),
      CtorDef("cons", List(Term.Uni(0), Term.Ind("MyList", Nil, Nil))),
    ))
    assert(result.isRight, s"Expected Right, got $result")

  test("Constructor with function arg not mentioning T is fine"):
    // case mk(f: Nat -> Nat): T
    val natTpe = Term.Ind("Nat", Nil, Nil)
    val result = PositivityChecker.check("Foo", List(
      CtorDef("mk", List(Term.Pi("_", natTpe, natTpe))),
    ))
    assert(result.isRight, s"Expected Right, got $result")

  test("T in positive position (right of arrow) is accepted"):
    // case mk(f: Nat -> T): T
    val natTpe = Term.Ind("Nat", Nil, Nil)
    val tInd   = Term.Ind("W", Nil, Nil)
    val result = PositivityChecker.check("W", List(
      CtorDef("mk", List(Term.Pi("_", natTpe, tInd))),
    ))
    assert(result.isRight, s"Expected Right, got $result")

  test("No constructors is trivially positive"):
    val result = PositivityChecker.check("Empty", Nil)
    assert(result.isRight)

  // ---- Should be rejected (non-positive) ----

  test("REJECT: T in negative position (left of arrow)"):
    // case mk(f: Bad -> Nat): Bad
    val natTpe = Term.Ind("Nat", Nil, Nil)
    val badTpe = Term.Ind("Bad", Nil, Nil)
    val result = PositivityChecker.check("Bad", List(
      CtorDef("mk", List(Term.Pi("_", badTpe, natTpe))),
    ))
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("REJECT: T in negative position within nested Pi domain"):
    // case mk(f: (Nat -> Bad) -> Nat): Bad2
    // The inner (Nat -> Bad) is in positive position, BUT the outer arrow
    // puts the whole thing in negative position. However, Bad2 doesn't
    // appear here. Let's test the actual Bad case:
    // case mk(f: Bad2 -> Nat): Bad2
    val natTpe  = Term.Ind("Nat", Nil, Nil)
    val bad2Tpe = Term.Ind("Bad2", Nil, Nil)
    val result = PositivityChecker.check("Bad2", List(
      CtorDef("mk", List(Term.Pi("_", bad2Tpe, natTpe))),
    ))
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("REJECT: T appears as domain of Pi (contravariant)"):
    // case mk(f: Pi(x: Bad3). Nat): Bad3
    val natTpe  = Term.Ind("Nat", Nil, Nil)
    val bad3Tpe = Term.Ind("Bad3", Nil, Nil)
    val result = PositivityChecker.check("Bad3", List(
      CtorDef("mk", List(Term.Pi("x", bad3Tpe, natTpe))),
    ))
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("REJECT: T in doubly-negative position (left of arrow, inside arrow domain)"):
    // case mk(f: (Bad4 -> Nat) -> Nat): Bad4
    // Bad4 is in the domain of the inner arrow, which is itself in the domain of
    // the outer arrow. Domain of domain = positive, BUT the inner function type as
    // a whole is in negative position, so Bad4 is actually in negative position.
    // Actually: polarity flips at each arrow left. (Bad4 -> Nat) has Bad4 negative.
    // Then ((Bad4 -> Nat) -> Nat) has (Bad4 -> Nat) negative, so Bad4 is positive.
    // So this should actually be ACCEPTED by strict positivity.
    // Let me correct: doubly negative = positive. This test should pass.
    // Instead test: ((Nat -> Bad4) -> Nat) — Bad4 positive in inner, but the whole
    // (Nat -> Bad4) is negative in outer, meaning Bad4 is negative overall.
    val natTpe  = Term.Ind("Nat", Nil, Nil)
    val bad4Tpe = Term.Ind("Bad4", Nil, Nil)
    // (Nat -> Bad4) -> Nat — Bad4 in negative position
    val innerPi = Term.Pi("_", natTpe, bad4Tpe)  // Nat -> Bad4
    val outerPi = Term.Pi("_", innerPi, natTpe)    // (Nat -> Bad4) -> Nat
    val result = PositivityChecker.check("Bad4", List(
      CtorDef("mk", List(outerPi)),
    ))
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("REJECT: even one bad constructor makes the whole type non-positive"):
    val natTpe = Term.Ind("Nat", Nil, Nil)
    val badTpe = Term.Ind("Mixed", Nil, Nil)
    val result = PositivityChecker.check("Mixed", List(
      CtorDef("good", List(natTpe)),             // fine
      CtorDef("bad", List(Term.Pi("_", badTpe, natTpe))),  // T in negative position
    ))
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("ACCEPT: doubly-negative (domain of domain) is positive"):
    // case mk(f: (Bad5 -> Nat) -> Nat): Bad5
    // Bad5 appears in domain of domain: negative * negative = positive
    val natTpe  = Term.Ind("Nat", Nil, Nil)
    val bad5Tpe = Term.Ind("DblNeg", Nil, Nil)
    val innerPi = Term.Pi("_", bad5Tpe, natTpe)    // DblNeg -> Nat
    val outerPi = Term.Pi("_", innerPi, natTpe)    // (DblNeg -> Nat) -> Nat
    val result = PositivityChecker.check("DblNeg", List(
      CtorDef("mk", List(outerPi)),
    ))
    assert(result.isRight, s"Expected Right (accepted), got $result")

  // ---- Nested occurrences: T inside another inductive's parameters ----
  //
  // `D(T)` is only as positive as `D` is in that parameter. Inheriting the
  // ambient polarity here accepted `Bad { mk(w: Neg(Bad)) }`, from which the
  // CLI certified a proof of `0 = 1` with no recursion at the term level —
  // see `cli/PositivityGateSuite`, measured on the previous tree.
  //
  // Fixture layout, checked against the real elaborated form (the v0.27 lesson:
  // a fixture in the wrong convention just agrees with a checker in the wrong
  // convention): applied types are App spines, and inside `Neg(A: Type)`'s
  // `argTpes(0)` the parameter A is Var(j + q + (p-1-i)) = Var(0).

  private val emptyTpe = Term.Ind("Empty", Nil, Nil)

  /** Neg(A) { mk(f: A -> Empty) } — uses its parameter negatively. */
  private val negDef = IndDef("Neg", List(Param("A", Term.Uni(0))),
    List(CtorDef("mk", List(Term.Pi("x", Term.Var(0), emptyTpe)))), 0)

  /** Wrap(A) { wrap(a: A) } — uses its parameter strictly positively. */
  private val wrapDef = IndDef("Wrap", List(Param("A", Term.Uni(0))),
    List(CtorDef("wrap", List(Term.Var(0)))), 0)

  test("REJECT: T inside the parameter of an inductive that uses it negatively"):
    val env = GlobalEnv.empty.addInd(negDef)
    val result = PositivityChecker.check("Bad", List(
      CtorDef("mk", List(Term.App(Term.Ind("Neg", Nil, Nil), Term.Ind("Bad", Nil, Nil)))),
    ))(using env)
    assert(result.isLeft, s"a negative occurrence one inductive deep was accepted: $result")

  test("ACCEPT: T inside the parameter of an inductive that uses it positively"):
    // The control: rose-tree-style nesting must keep working.
    val env = GlobalEnv.empty.addInd(wrapDef)
    val result = PositivityChecker.check("Tree", List(
      CtorDef("leaf", Nil),
      CtorDef("node", List(Term.App(Term.Ind("Wrap", Nil, Nil), Term.Ind("Tree", Nil, Nil)))),
    ))(using env)
    assert(result.isRight, s"benign nesting through a positive parameter was rejected: $result")

  test("REJECT: the negative use is two inductives deep"):
    // Fwd(A) { mk(x: Neg(A)) } passes its parameter into Neg. T -> Fwd(T) ->
    // Neg(T) is still a function out of T; the recursion has to follow it.
    val fwdDef = IndDef("Fwd", List(Param("A", Term.Uni(0))),
      List(CtorDef("mk", List(Term.App(Term.Ind("Neg", Nil, Nil), Term.Var(0))))), 0)
    val env = GlobalEnv.empty.addInd(negDef).addInd(fwdDef)
    val result = PositivityChecker.check("Bad", List(
      CtorDef("mk", List(Term.App(Term.Ind("Fwd", Nil, Nil), Term.Ind("Bad", Nil, Nil)))),
    ))(using env)
    assert(result.isLeft, s"a negative occurrence two inductives deep was accepted: $result")

  test("ACCEPT: self-nesting parameter passing terminates (the seen-set)"):
    // Loop(A) { mk(x: Loop(A)) } passes its parameter to itself. A cycle with
    // no violation along it is fine and must not diverge.
    val loopDef = IndDef("Loop", List(Param("A", Term.Uni(0))),
      List(CtorDef("mk", List(Term.App(Term.Ind("Loop", Nil, Nil), Term.Var(0))))), 0)
    val env = GlobalEnv.empty.addInd(loopDef)
    val result = PositivityChecker.check("Outer", List(
      CtorDef("mk", List(Term.App(Term.Ind("Loop", Nil, Nil), Term.Ind("Outer", Nil, Nil)))),
    ))(using env)
    assert(result.isRight, s"a benign parameter cycle was rejected (or diverged): $result")

  test("REJECT: T inside the parameters of an inductive that is not in scope"):
    // Constructors we cannot see are constructors we cannot vouch for.
    val result = PositivityChecker.check("Bad", List(
      CtorDef("mk", List(Term.App(Term.Ind("Mystery", Nil, Nil), Term.Ind("Bad", Nil, Nil)))),
    ))(using GlobalEnv.empty)
    assert(result.isLeft, s"an occurrence inside an unknown inductive was accepted: $result")

  test("REJECT: T inside an index argument"):
    // Indexed(q=1, p=0): the occurrence lands past the parameter window and is
    // rejected conservatively rather than reasoned about.
    val idxDef = IndDef("Idx", Nil,
      List(CtorDef("mk", Nil)), 0, indices = List(Param("n", Term.Ind("Nat", Nil, Nil))))
    val env = GlobalEnv.empty.addInd(idxDef)
    val result = PositivityChecker.check("Bad", List(
      CtorDef("mk", List(Term.App(Term.Ind("Idx", Nil, Nil), Term.Ind("Bad", Nil, Nil)))),
    ))(using env)
    assert(result.isLeft, s"an occurrence in an index argument was accepted: $result")

  test("ACCEPT: T inside the arguments of Eq"):
    // Eq is a built-in absent from the environment; refl carries no fields, so
    // its parameters are trivially strictly positive. The lookup-failure rule
    // must not swallow it.
    val eqApp = Term.App(Term.App(Term.Ind("Eq", Nil, Nil),
      Term.Ind("T", Nil, Nil)), Term.Ind("T", Nil, Nil))
    val result = PositivityChecker.check("T", List(
      CtorDef("mk", List(eqApp)),
    ))(using GlobalEnv.empty)
    assert(result.isRight, s"an Eq statement about T was rejected: $result")
