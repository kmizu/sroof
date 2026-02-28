package sproof.checker

import sproof.core.{Term, Context, GlobalEnv}
import munit.FunSuite

/** Tests for universe cumulativity: Type_i ≤ Type_{i+1}.
 *
 *  In predicative CIC with cumulativity, a term of type Type_i can be used
 *  where Type_{i+1} (or higher) is expected. This allows more natural
 *  definitions without manual universe lifting.
 *
 *  Example: if A : Type and B : Type1, then (A -> B) : Type1
 *  and A should be accepted where Type1 is expected.
 */
class CumulativitySuite extends FunSuite:

  given GlobalEnv = GlobalEnv.empty

  // ---- Should pass with cumulativity ----

  test("Type0 is accepted where Type1 is expected"):
    // check(ctx, Type0, Type1) should succeed with cumulativity
    val result = Bidirectional.check(Context.empty, Term.Uni(0), Term.Uni(1))
    assert(result.isRight, s"Type0 should be accepted as Type1: $result")

  test("Type0 is accepted where Type2 is expected (multi-level)"):
    val result = Bidirectional.check(Context.empty, Term.Uni(0), Term.Uni(2))
    assert(result.isRight, s"Type0 should be accepted as Type2: $result")

  test("Type1 is accepted where Type2 is expected"):
    val result = Bidirectional.check(Context.empty, Term.Uni(1), Term.Uni(2))
    assert(result.isRight, s"Type1 should be accepted as Type2: $result")

  test("same universe level still works"):
    // Type0 : Type1 (this already works)
    val result = Bidirectional.infer(Context.empty, Term.Uni(0))
    assertEquals(result, Right(Term.Uni(1)))

  // ---- Should still fail ----

  test("REJECT: Type1 where Type0 is expected (no downward cumulativity)"):
    val result = Bidirectional.check(Context.empty, Term.Uni(1), Term.Uni(0))
    assert(result.isLeft, s"Type1 should NOT be accepted as Type0: $result")

  test("REJECT: Type2 where Type1 is expected"):
    val result = Bidirectional.check(Context.empty, Term.Uni(2), Term.Uni(1))
    assert(result.isLeft, s"Type2 should NOT be accepted as Type1: $result")

  test("lambda value is not a universe (not affected by cumulativity)"):
    // λx.x should not be accepted as Type0
    val lam = Term.Lam("x", Term.Uni(0), Term.Var(0))
    val result = Bidirectional.check(Context.empty, lam, Term.Uni(0))
    assert(result.isLeft, s"lambda should not be accepted as Type0")
