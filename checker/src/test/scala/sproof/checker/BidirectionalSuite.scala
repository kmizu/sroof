package sproof.checker

import sproof.core.{Term, Context}

class BidirectionalSuite extends munit.FunSuite:

  val empty = Context.empty

  def ok(t: Term, ctx: Context = empty): Term =
    Bidirectional.infer(ctx, t).fold(e => fail(e.getMessage), identity)

  def chk(t: Term, tp: Term, ctx: Context = empty): Unit =
    Bidirectional.check(ctx, t, tp).fold(e => fail(e.getMessage), identity)

  def err(t: Term, ctx: Context = empty): TypeError =
    Bidirectional.infer(ctx, t).fold(identity, v => fail(s"Expected error, got $v"))

  // --- Universe ---
  test("Type0 : Type1"):
    assertEquals(ok(Term.Uni(0)), Term.Uni(1))

  test("Type1 : Type2"):
    assertEquals(ok(Term.Uni(1)), Term.Uni(2))

  // --- Var ---
  test("Var(0) in ctx[x:Type0] : Type0"):
    val ctx = empty.extend("x", Term.Uni(0))
    assertEquals(ok(Term.Var(0), ctx), Term.Uni(0))

  test("Var(0): unbound in empty context"):
    assert(err(Term.Var(0)).isInstanceOf[TypeError.UnboundVariable])

  test("Var(1) in ctx[y:Type1, x:Type0] : Type0 (shifted)"):
    val ctx = empty.extend("x", Term.Uni(0)).extend("y", Term.Uni(1))
    val tp  = ok(Term.Var(1), ctx)
    assertEquals(tp, Term.Uni(0))

  // --- Pi ---
  // Pi(x:A, B) : Type_{max(l_A, l_B)} where A:Type_{l_A}, B:Type_{l_B}
  // Uni(i) : Uni(i+1), so l_{Uni(i)} = i+1
  test("Pi(x:Type0, Type0) : Type1  [max(1,1)=1]"):
    assertEquals(ok(Term.Pi("x", Term.Uni(0), Term.Uni(0))), Term.Uni(1))

  test("Pi(x:Type1, Type0) : Type2  [max(2,1)=2]"):
    assertEquals(ok(Term.Pi("x", Term.Uni(1), Term.Uni(0))), Term.Uni(2))

  test("Pi(x:Type0, Type1) : Type2  [max(1,2)=2]"):
    assertEquals(ok(Term.Pi("x", Term.Uni(0), Term.Uni(1))), Term.Uni(2))

  // --- Lam ---
  // λx:Type0. x : Pi(x:Type0, Type0)  — identity on Type0 inhabitants
  // Type of body in extCtx: Var(0) has type Uni(0), so Pi cod = Uni(0)
  test("λx:Type0. x : Pi(x:Type0, Type0)"):
    val t  = Term.Lam("x", Term.Uni(0), Term.Var(0))
    val tp = ok(t)
    assertEquals(tp, Term.Pi("x", Term.Uni(0), Term.Uni(0)))

  // λx:Type0. Type0 : Pi(x:Type0, Type1)  — constant Type0 has type Uni(1)
  test("λx:Type0. Type0 : Pi(x:Type0, Type1)"):
    val t  = Term.Lam("x", Term.Uni(0), Term.Uni(0))
    val tp = ok(t)
    assertEquals(tp, Term.Pi("x", Term.Uni(0), Term.Uni(1)))

  // --- App ---
  // (λx:Type1. x) Type0 → result type = cod subst arg = Uni(1) subst Uni(0) = Uni(1)
  // (Type0 : Type1, so this typechecks; result = Type1 since identity on Type1-things)
  test("(λx:Type1. x) Type0 : Type1"):
    val lam = Term.Lam("x", Term.Uni(1), Term.Var(0))
    assertEquals(ok(Term.App(lam, Term.Uni(0))), Term.Uni(1))

  test("App of non-function: NotAFunction error"):
    assert(err(Term.App(Term.Uni(0), Term.Uni(0))).isInstanceOf[TypeError.NotAFunction])

  // Applying identity (Type0→Type0) to Type0 fails: Type0:Type1 ≠ Type0
  test("(λx:Type0. x) Type0 : fails (Type0:Type1, not Type0)"):
    val lam = Term.Lam("x", Term.Uni(0), Term.Var(0))
    assert(Bidirectional.infer(empty, Term.App(lam, Term.Uni(0))).isLeft)

  // --- Check mode ---
  // λx:Type0. x against non-dependent Pi(Type0, Type0) = Type0 → Type0
  test("check (λx:Type0. x) against (Type0 → Type0)"):
    chk(Term.Lam("x", Term.Uni(0), Term.Var(0)), Term.Pi("x", Term.Uni(0), Term.Uni(0)))

  test("check Type0 against Type1"):
    chk(Term.Uni(0), Term.Uni(1))

  test("check Type1 against Type0: type mismatch"):
    assert(Bidirectional.check(empty, Term.Uni(1), Term.Uni(0)).isLeft)

  // --- Let ---
  // let x:Type1 = Type0 in x — x has type Type1, so result type is Type1
  test("let x:Type1 = Type0 in x : Type1"):
    val t = Term.Let("x", Term.Uni(1), Term.Uni(0), Term.Var(0))
    assertEquals(ok(t), Term.Uni(1))

  // --- Fix ---
  test("fix n:Type0. n : Type0"):
    val t = Term.Fix("n", Term.Uni(0), Term.Var(0))
    assertEquals(ok(t), Term.Uni(0))

  // --- Conversion check ---
  // (λx:Type1. x) Type0 has type Type1 (≡ Uni(1)); check against Uni(1) succeeds
  test("beta-equivalent types: (λx:Type1. x) Type0 check against Type1"):
    val t = Term.App(Term.Lam("x", Term.Uni(1), Term.Var(0)), Term.Uni(0))
    chk(t, Term.Uni(1))

  // (λx:Type2. x) (Type0 → Type0) has type Type2 ← via beta reduction + cumulativity
  test("beta reduction via check: identity applied to Pi type"):
    val piTy = Term.Pi("_", Term.Uni(0), Term.Uni(0))  // Type0 → Type0 : Type1
    val t    = Term.App(Term.Lam("x", Term.Uni(2), Term.Var(0)), piTy)
    // piTy : Type1, identity expects Type2; succeeds via cumulativity (Type1 ≤ Type2)
    assert(Bidirectional.infer(empty, t).isRight)

  // --- universe overflow ---
  test("Uni(101): overflow error"):
    assert(err(Term.Uni(101)).isInstanceOf[TypeError.UniverseOverflow])
