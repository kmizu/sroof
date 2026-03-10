package sroof.checker

import sroof.core.{Term, Context, GlobalEnv, MatchCase}
import munit.FunSuite

/** TDD tests for inductive type checking (Con + Mat).
 *
 *  Written BEFORE IndChecker implementation (RED phase).
 *  Tests cover:
 *  1. Constructor type inference (Con)
 *  2. Pattern match type checking (Mat)
 *  3. Soundness: wrong types are rejected
 */
class IndCheckerSuite extends FunSuite:

  given GlobalEnv = GlobalEnv.withNat
  val ctx    = Context.empty
  val natTpe = Term.Ind("Nat", Nil, Nil)

  // ======== Con: type inference ========

  test("Nat.zero has type Nat"):
    val zero = Term.Con("zero", "Nat", Nil)
    assertEquals(Bidirectional.infer(ctx, zero), Right(natTpe))

  test("Nat.succ(zero) has type Nat"):
    val zero     = Term.Con("zero", "Nat", Nil)
    val succZero = Term.Con("succ", "Nat", List(zero))
    assertEquals(Bidirectional.infer(ctx, succZero), Right(natTpe))

  test("Nat.succ(succ(zero)) has type Nat — nested constructor"):
    val zero        = Term.Con("zero", "Nat", Nil)
    val succ_zero   = Term.Con("succ", "Nat", List(zero))
    val succ2_zero  = Term.Con("succ", "Nat", List(succ_zero))
    assert(Bidirectional.infer(ctx, succ2_zero).isRight)

  test("SOUNDNESS: Nat.succ(Type0) fails — wrong argument type"):
    val bad = Term.Con("succ", "Nat", List(Term.Uni(0)))
    assert(Bidirectional.infer(ctx, bad).isLeft)

  test("SOUNDNESS: Nat.succ with no args fails — wrong arg count"):
    val bad = Term.Con("succ", "Nat", Nil)
    assert(Bidirectional.infer(ctx, bad).isLeft)

  test("SOUNDNESS: Nat.zero with extra arg fails — wrong arg count"):
    val bad = Term.Con("zero", "Nat", List(Term.Uni(0)))
    assert(Bidirectional.infer(ctx, bad).isLeft)

  test("SOUNDNESS: unknown constructor fails"):
    val bad = Term.Con("bogus", "Nat", Nil)
    assert(Bidirectional.infer(ctx, bad).isLeft)

  test("SOUNDNESS: unknown inductive type fails"):
    val bad = Term.Con("zero", "Foo", Nil)
    assert(Bidirectional.infer(ctx, bad).isLeft)

  // ======== Mat: type checking ========

  test("Mat on Nat: pred function (zero → zero, succ k → k) type-checks"):
    // fun n => match n { case zero => zero; case succ(k) => k }
    val ctxWithN = ctx.extend("n", natTpe)
    val cases = List(
      MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      MatchCase("succ", 1, Term.Var(0)),  // k = Var(0)
    )
    val mat = Term.Mat(Term.Var(0), cases, natTpe)
    assert(Bidirectional.infer(ctxWithN, mat).isRight)

  test("Mat on Nat: identity (succ(k)) type-checks"):
    // match n { case zero => zero; case succ(k) => succ(k) }
    val ctxWithN = ctx.extend("n", natTpe)
    val cases = List(
      MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      MatchCase("succ", 1, Term.Con("succ", "Nat", List(Term.Var(0)))),
    )
    val mat = Term.Mat(Term.Var(0), cases, natTpe)
    assert(Bidirectional.infer(ctxWithN, mat).isRight)

  test("Mat on Nat: match return type is the declared returnTpe"):
    val ctxWithN = ctx.extend("n", natTpe)
    val cases = List(
      MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      MatchCase("succ", 1, Term.Var(0)),
    )
    val mat = Term.Mat(Term.Var(0), cases, natTpe)
    assertEquals(Bidirectional.infer(ctxWithN, mat), Right(natTpe))

  test("SOUNDNESS: Mat on Nat: missing branch fails"):
    val ctxWithN = ctx.extend("n", natTpe)
    val cases = List(
      MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      // missing succ case!
    )
    val mat = Term.Mat(Term.Var(0), cases, natTpe)
    assert(Bidirectional.infer(ctxWithN, mat).isLeft)

  test("SOUNDNESS: Mat on Nat: wrong body type fails"):
    // zero case returns Type0 instead of Nat
    val ctxWithN = ctx.extend("n", natTpe)
    val cases = List(
      MatchCase("zero", 0, Term.Uni(0)),  // Type0, not Nat!
      MatchCase("succ", 1, Term.Var(0)),
    )
    val mat = Term.Mat(Term.Var(0), cases, natTpe)
    assert(Bidirectional.infer(ctxWithN, mat).isLeft)

  test("SOUNDNESS: Mat on Nat: unknown case constructor fails"):
    val ctxWithN = ctx.extend("n", natTpe)
    val cases = List(
      MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
      MatchCase("succ", 1, Term.Var(0)),
      MatchCase("bogus", 0, Term.Con("zero", "Nat", Nil)),  // unknown ctor
    )
    val mat = Term.Mat(Term.Var(0), cases, natTpe)
    assert(Bidirectional.infer(ctxWithN, mat).isLeft)
