package sroof.checker

import sroof.core.{Term, Context, GlobalEnv, MatchCase, IndDef, CtorDef, Param}
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

  // ======== Indexed families ========
  //
  // These build the `IndDef` directly rather than going through the parser,
  // because the case that matters most here cannot be written in `.sroof` syntax:
  // a family with indices but *no* parameters. `Bidirectional`'s check-mode route
  // for constructors is guarded on `params.nonEmpty`, so such a family is typed by
  // `inferCon` — a different branch from the one `cli/IndexedFamilySuite` covers.

  /** `Flag()(n: Nat)`: `off` is index 0, `on` is index 1. No parameters. */
  private val flagDef = IndDef(
    name    = "Flag",
    params  = Nil,
    ctors   = List(
      CtorDef("off", Nil, List(Term.Con("zero", "Nat", Nil))),
      CtorDef("on",  Nil, List(Term.Con("succ", "Nat", List(Term.Con("zero", "Nat", Nil))))),
    ),
    universe = 0,
    indices  = List(Param("n", natTpe)),
  )
  private val flagEnv                = GlobalEnv.withNat.addInd(flagDef)
  private def flag(idx: Term): Term  = Term.App(Term.Ind("Flag", Nil, Nil), idx)
  private val zero                   = Term.Con("zero", "Nat", Nil)
  private val one                    = Term.Con("succ", "Nat", List(zero))

  test("indexed, parameterless: each constructor infers its own index"):
    given GlobalEnv = flagEnv
    assertEquals(Bidirectional.infer(ctx, Term.Con("off", "Flag", Nil)), Right(flag(zero)))
    assertEquals(Bidirectional.infer(ctx, Term.Con("on",  "Flag", Nil)), Right(flag(one)))

  test("SOUNDNESS: indexed, parameterless: a constructor cannot borrow another's index"):
    given GlobalEnv = flagEnv
    // The accepting half is asserted first and deliberately: before v0.10 this
    // family's constructors inferred the bare head `Ind("Flag")`, so *nothing*
    // checked against an applied type and the rejection below would have held for
    // the wrong reason.
    assert(
      Bidirectional.check(ctx, Term.Con("off", "Flag", Nil), flag(zero)).isRight,
      "`off` must check against its own index",
    )
    assert(
      Bidirectional.check(ctx, Term.Con("off", "Flag", Nil), flag(one)).isLeft,
      "`off` has index 0 and must not check against index 1",
    )

  test("backward compatibility: indices without declared return indices are phantom"):
    // Exactly the shape of every declaration written before v0.10: `indices` is
    // populated, `retIndices` is empty everywhere. There is nothing to derive, so
    // the inferred type must stay the bare head it has always been — not
    // `Ind(...)` applied to a guess.
    val phantomDef = flagDef.copy(
      name  = "Phantom",
      ctors = List(CtorDef("only", Nil, Nil)),
    )
    given GlobalEnv = GlobalEnv.withNat.addInd(phantomDef)
    assertEquals(
      Bidirectional.infer(ctx, Term.Con("only", "Phantom", Nil)),
      Right(Term.Ind("Phantom", Nil, Nil)),
    )

  test("a half-annotated family is treated as un-indexed, not partly indexed"):
    // If only some constructors state their index, deriving indices for those and
    // nothing for the rest would give the family two different arities. Fall back
    // to the pre-v0.10 reading instead.
    val halfDef = flagDef.copy(
      name  = "Half",
      ctors = List(
        CtorDef("stated", Nil, List(zero)),
        CtorDef("silent", Nil, Nil),
      ),
    )
    given GlobalEnv = GlobalEnv.withNat.addInd(halfDef)
    assertEquals(
      Bidirectional.infer(ctx, Term.Con("stated", "Half", Nil)),
      Right(Term.Ind("Half", Nil, Nil)),
    )
