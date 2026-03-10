package sroof.tactic

import sroof.core.{Term, Context, GlobalEnv, MatchCase}
import munit.FunSuite

/** TDD tests for the `induction` and `simplify` tactics.
 *
 *  Written BEFORE implementation (RED phase).
 *  Uses GlobalEnv.withNat for inductive type information.
 */
class InductionSuite extends FunSuite:

  given GlobalEnv = GlobalEnv.withNat
  val natTpe = Term.Ind("Nat", Nil, Nil)

  // Helper: build a context with n : Nat
  def ctxN: Context = Context.empty.extend("n", natTpe)

  // Helper to run a tactic and return the proof term
  def prove(ctx: Context, goal: Term)(t: TacticM[Unit]): Either[TacticError, Term] =
    TacticM.prove(ctx, goal)(t)

  // ======== induction ========

  test("induction on Nat generates 2 subgoals"):
    // Goal: n = n (any non-trivial goal that requires case split)
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Var(0))
    var goalCount = 0
    val result = prove(ctxN, goal) {
      for
        _ <- Builtins.induction("n")
        // After induction: 2 subgoals
        gp1 <- TacticM.currentGoal
        _    = { goalCount += 1; () }
        (mv1, g1) = gp1
        _   <- TacticM.solveGoalWith(mv1, Eq.mkRefl(Term.Con("zero", "Nat", Nil)))
        gp2 <- TacticM.currentGoal
        _    = { goalCount += 1; () }
        (mv2, g2) = gp2
        _   <- TacticM.solveGoalWith(mv2, Eq.mkRefl(Term.Con("succ", "Nat", List(Term.Var(0)))))
      yield ()
    }
    assertEquals(goalCount, 2, "Expected 2 subgoals from induction")
    assert(result.isRight, s"Expected proof success, got $result")

  test("induction zero-case goal is specialized: G[n → zero]"):
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Var(0))
    var zeroGoal: Option[Goal] = None
    prove(ctxN, goal) {
      for
        _ <- Builtins.induction("n")
        gp1 <- TacticM.currentGoal
        _ = { zeroGoal = Some(gp1._2); () }
        (mv1, _) = gp1
        _ <- TacticM.solveGoalWith(mv1, Eq.mkRefl(Term.Con("zero", "Nat", Nil)))
        gp2 <- TacticM.currentGoal
        (mv2, _) = gp2
        _ <- TacticM.solveGoalWith(mv2, Eq.mkRefl(Term.Con("succ", "Nat", List(Term.Var(0)))))
      yield ()
    }
    zeroGoal match
      case None => fail("No zero case goal captured")
      case Some(g) =>
        // Goal should be Eq(Nat, zero, zero)
        val expectedGoal = Eq.mkType(natTpe,
          Term.Con("zero", "Nat", Nil),
          Term.Con("zero", "Nat", Nil),
        )
        assertEquals(g.target, expectedGoal,
          s"Zero case goal should be Eq(Nat, zero, zero), got ${g.target.show}")

  test("induction succ-case goal is specialized: G[n → succ(k)]"):
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Var(0))
    var succGoal: Option[Goal] = None
    prove(ctxN, goal) {
      for
        _ <- Builtins.induction("n")
        gp1 <- TacticM.currentGoal
        (mv1, _) = gp1
        _ <- TacticM.solveGoalWith(mv1, Eq.mkRefl(Term.Con("zero", "Nat", Nil)))
        gp2 <- TacticM.currentGoal
        _ = { succGoal = Some(gp2._2); () }
        (mv2, _) = gp2
        _ <- TacticM.solveGoalWith(mv2, Eq.mkRefl(Term.Con("succ", "Nat", List(Term.Var(0)))))
      yield ()
    }
    succGoal match
      case None => fail("No succ case goal captured")
      case Some(g) =>
        // Goal should be Eq(Nat, succ(Var(0)), succ(Var(0))) in ctx [k: Nat]
        // Var(0) = k (possibly Var(1) = k if IH is added too)
        // At minimum: it must mention succ somewhere
        assert(g.target.show.contains("succ"),
          s"Succ case goal should mention succ, got ${g.target.show}")

  test("induction succ-case context contains k: Nat"):
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Var(0))
    var succGoal: Option[Goal] = None
    prove(ctxN, goal) {
      for
        _ <- Builtins.induction("n")
        gp1 <- TacticM.currentGoal
        (mv1, _) = gp1
        _ <- TacticM.solveGoalWith(mv1, Eq.mkRefl(Term.Con("zero", "Nat", Nil)))
        gp2 <- TacticM.currentGoal
        _ = { succGoal = Some(gp2._2); () }
        (mv2, _) = gp2
        _ <- TacticM.solveGoalWith(mv2, Eq.mkRefl(Term.Con("succ", "Nat", List(Term.Var(0)))))
      yield ()
    }
    succGoal match
      case None => fail("No succ case goal captured")
      case Some(g) =>
        // Context should have at least one more entry than empty (k: Nat)
        assert(g.ctx.size >= 1, s"Succ case context should have k: Nat, size = ${g.ctx.size}")
        // The innermost variable (Var(0)) should have type Nat
        assertEquals(g.ctx.lookup(0), Some(natTpe),
          s"Var(0) in succ case context should have type Nat")

  test("SOUNDNESS: induction on non-inductive type fails"):
    // Goal: Type0 = Type0; try to do induction on a variable of type Type0
    val ctx = Context.empty.extend("x", Term.Uni(0))
    val goal = Eq.mkType(Term.Uni(1), Term.Uni(0), Term.Uni(0))
    val result = prove(ctx, goal)(Builtins.induction("x"))
    assert(result.isLeft, "induction on non-inductive type should fail")

  test("SOUNDNESS: induction on unknown variable fails"):
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Var(0))
    val result = prove(ctxN, goal)(Builtins.induction("bogus"))
    assert(result.isLeft, "induction on unknown variable should fail")

  // ======== e2e: n = n by induction ========

  test("e2e: n = n proof by induction on Nat with trivial"):
    // defspec eq_refl(n: Nat): n = n
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Var(0))
    val result = prove(ctxN, goal) {
      for
        _  <- Builtins.induction("n")
        // Case 1: zero — prove zero = zero
        gp1 <- TacticM.currentGoal
        (mv1, g1) = gp1
        _  <- Builtins.trivial
        // Case 2: succ(k) — prove succ(k) = succ(k)
        gp2 <- TacticM.currentGoal
        (mv2, g2) = gp2
        _  <- Builtins.trivial
      yield ()
    }
    assert(result.isRight, s"n = n proof by induction should succeed, got $result")

  // ======== simplify ========

  test("simplify closes a trivially true goal"):
    // simplify should at minimum close Eq(Nat, zero, zero)
    val ctx = Context.empty
    val goal = Eq.mkType(natTpe, Term.Con("zero", "Nat", Nil), Term.Con("zero", "Nat", Nil))
    val result = prove(ctx, goal)(Builtins.simplify(Nil))
    assert(result.isRight, s"simplify should close zero = zero, got $result")

  test("simplify closes a goal after NbE reduction"):
    // (λx. x) zero = zero  →  NbE reduces to zero = zero → trivial
    val lhs = Term.App(Term.Lam("x", natTpe, Term.Var(0)), Term.Con("zero", "Nat", Nil))
    val rhs = Term.Con("zero", "Nat", Nil)
    val goal = Eq.mkType(natTpe, lhs, rhs)
    val result = prove(Context.empty, goal)(Builtins.simplify(Nil))
    assert(result.isRight, s"simplify should close (λx.x) zero = zero, got $result")

  test("simplify fails on non-trivial goal"):
    // n = zero for abstract n should fail
    val goal = Eq.mkType(natTpe, Term.Var(0), Term.Con("zero", "Nat", Nil))
    val result = prove(ctxN, goal)(Builtins.simplify(Nil))
    assert(result.isLeft, "simplify should fail on n = zero for abstract n")
