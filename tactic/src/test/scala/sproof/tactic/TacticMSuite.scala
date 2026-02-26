package sproof.tactic

import sproof.core.{Term, Context}
import munit.FunSuite

/** Tests for the TacticM proof monad infrastructure.
 *
 *  TDD: these tests are written before the implementation.
 *  They define the expected API and behaviour of the monad.
 */
class TacticMSuite extends FunSuite:

  val empty: Context = Context.empty

  // --- pure and fail ---

  test("pure returns value without changing state"):
    val (state, result) = TacticM.run(TacticM.pure(42), ProofState.empty)
    assertEquals(result, Right(42))
    assertEquals(state, ProofState.empty)

  test("fail returns the given error"):
    val err = TacticError.NoGoals
    val (_, result) = TacticM.run(TacticM.fail[Int](err), ProofState.empty)
    assertEquals(result, Left(TacticError.NoGoals))

  // --- currentGoal ---

  test("currentGoal on empty state fails with NoGoals"):
    val (_, result) = TacticM.run(TacticM.currentGoal, ProofState.empty)
    assertEquals(result, Left(TacticError.NoGoals))

  test("currentGoal returns first goal when goals exist"):
    val goal  = Goal(empty, Term.Uni(0))
    val mv    = MetaVar(0)
    val state = ProofState(List(mv -> goal), Map.empty, 1)
    val (_, result) = TacticM.run(TacticM.currentGoal, state)
    assertEquals(result, Right(mv -> goal))

  test("currentGoal returns first of multiple goals"):
    val g1 = Goal(empty, Term.Uni(0))
    val g2 = Goal(empty, Term.Uni(1))
    val mv1 = MetaVar(0); val mv2 = MetaVar(1)
    val state = ProofState(List(mv1 -> g1, mv2 -> g2), Map.empty, 2)
    val (_, result) = TacticM.run(TacticM.currentGoal, state)
    assertEquals(result, Right(mv1 -> g1))

  // --- solveGoalWith ---

  test("solveGoalWith removes goal and stores evidence"):
    val goal  = Goal(empty, Term.Uni(0))
    val mv    = MetaVar(0)
    val state = ProofState(List(mv -> goal), Map.empty, 1)
    val tactic = TacticM.currentGoal.flatMap { gp =>
      TacticM.solveGoalWith(gp._1, Term.Uni(0))
    }
    val (finalState, result) = TacticM.run(tactic, state)
    assertEquals(result, Right(()))
    assert(finalState.goals.isEmpty, "Goals should be empty after solving")
    assertEquals(finalState.evidence.get(mv), Some(Term.Uni(0)))

  test("solveGoalWith leaves other goals intact"):
    val g1 = Goal(empty, Term.Uni(0))
    val g2 = Goal(empty, Term.Uni(1))
    val mv1 = MetaVar(0); val mv2 = MetaVar(1)
    val state  = ProofState(List(mv1 -> g1, mv2 -> g2), Map.empty, 2)
    val tactic = TacticM.solveGoalWith(mv1, Term.Uni(0))
    val (finalState, _) = TacticM.run(tactic, state)
    assertEquals(finalState.goals.length, 1)
    assertEquals(finalState.goals.head._1, mv2)

  // --- addGoal ---

  test("addGoal adds a goal and returns its MetaVar"):
    val (state, result) = TacticM.run(TacticM.addGoal(empty, Term.Uni(0)), ProofState.empty)
    assertEquals(result, Right(MetaVar(0)))
    assertEquals(state.goals.length, 1)
    assertEquals(state.nextMeta, 1)
    assertEquals(state.goals.head._2, Goal(empty, Term.Uni(0)))

  test("addGoal increments nextMeta"):
    val initial = ProofState(Nil, Map.empty, 5)
    val (state, result) = TacticM.run(TacticM.addGoal(empty, Term.Uni(0)), initial)
    assertEquals(result, Right(MetaVar(5)))
    assertEquals(state.nextMeta, 6)

  // --- prove (top-level) ---

  test("prove creates initial state and returns evidence term"):
    val result = TacticM.prove(empty, Term.Uni(0)) {
      TacticM.currentGoal.flatMap { gp =>
        TacticM.solveGoalWith(gp._1, Term.Uni(0))
      }
    }
    assertEquals(result, Right(Term.Uni(0)))

  test("prove fails if goals remain unsolved"):
    val result = TacticM.prove(empty, Term.Uni(0)) {
      TacticM.pure(())  // does nothing — goal remains
    }
    assert(result.isLeft, s"Expected Left but got $result")

  test("prove fails if main goal was not solved"):
    val result = TacticM.prove(empty, Term.Uni(0)) {
      // Add a new goal but never solve the original
      TacticM.addGoal(empty, Term.Uni(1)).map(_ => ())
    }
    assert(result.isLeft)

  // --- monad laws: sequencing ---

  test("flatMap sequences tactics"):
    val tactic: TacticM[Int] =
      TacticM.pure(1).flatMap(x => TacticM.pure(x + 1))
    val (_, result) = TacticM.run(tactic, ProofState.empty)
    assertEquals(result, Right(2))

  test("fail short-circuits subsequent tactics"):
    var sideEffect = false
    val tactic: TacticM[Int] =
      TacticM.fail[Int](TacticError.NoGoals).flatMap { _ =>
        sideEffect = true
        TacticM.pure(42)
      }
    val (_, result) = TacticM.run(tactic, ProofState.empty)
    assert(result.isLeft)
    assert(!sideEffect, "Side effect should not have run after fail")
