package sproof.tactic

import sproof.core.{Term, Context, Subst}
import sproof.checker.Bidirectional
import sproof.eval.{Quote, Eval, Env, Semantic, Neutral}

/** Built-in tactics for sproof.
 *
 *  Naming philosophy: full English words as primary names,
 *  obvious abbreviations as aliases.  No cryptic shortcuts.
 *
 *    trivial  / triv    — close a reflexive equality goal
 *    assume   (no abbr) — introduce a Pi-bound variable
 *    apply_   (no abbr) — apply a function to reduce the goal
 *
 *  These tactics are NOT part of the trusted Kernel.  Every proof term
 *  they produce is subsequently re-checked by Kernel.check.
 */
object Builtins:

  // ---- trivial / triv ----

  /** Close an equality goal `Eq T a b` when `a` and `b` are definitionally equal.
   *
   *  Corresponds to `rfl` / `reflexivity` in Coq, but with a name that
   *  communicates intent: this goal is *trivially* true.
   */
  val trivial: TacticM[Unit] =
    for
      goalPair   <- TacticM.currentGoal
      (mv, goal)  = goalPair
      // Extract Eq structure from the raw term — do NOT whnf the outer goal because
      // NbE evaluation of Ind("Eq",...) loses the name and breaks pattern matching.
      // We normalise only the two sides (lhs, rhs) for the definitional equality check.
      result     <- Eq.extract(goal.target) match
        case None =>
          TacticM.fail(TacticError.NotAnEquality(goal.target.show))
        case Some(triple) =>
          val (_, lhs, rhs) = triple
          val env = buildEnv(goal.ctx)
          if Quote.convEqual(goal.ctx.size, env, lhs, rhs) then
            TacticM.solveGoalWith(mv, Eq.mkRefl(lhs))
          else
            TacticM.fail(TacticError.Custom(
              s"trivial: not definitionally equal: ${lhs.show} ≢ ${rhs.show}"
            ))
    yield result

  /** Alias for `trivial`. */
  val triv: TacticM[Unit] = trivial

  // ---- assume ----

  /** Introduce the outermost Pi binder as a local variable.
   *
   *  `assume "x"` on goal `Pi(y, A, B)` replaces the goal with `B`
   *  in an extended context that contains `x : A`.
   *
   *  Corresponds to `intro` / `intros` in Coq, but with a name that
   *  makes the action explicit: we *assume* `x : A`.
   */
  def assume(varName: String): TacticM[Unit] =
    for
      goalPair   <- TacticM.currentGoal
      (mv, goal)  = goalPair
      target      = Bidirectional.whnf(goal.ctx, goal.target)
      result     <- target match
        case Term.Pi(_, dom, cod) =>
          val newCtx    = goal.ctx.extend(varName, dom)
          // cod has Var(0) = the Pi-bound variable, which in newCtx is varName
          val newTarget = cod
          for
            mv_new <- TacticM.addGoal(newCtx, newTarget)
            // Evidence: λvarName. <proof of body> — body filled by mv_new
            _      <- TacticM.solveGoalWith(mv, Term.Lam(varName, dom, Term.Meta(mv_new.id)))
          yield ()
        case _ =>
          TacticM.fail(TacticError.NotAPi(goal.target.show))
    yield result

  // ---- apply ----

  /** Apply a function term to reduce the current goal.
   *
   *  `apply_ f` where `f : A → B` and the goal is `B`:
   *    - Unifies the codomain of `f` with the goal
   *    - Replaces the goal with the domain of `f`
   *    - Evidence for the original goal will be `f <evidence-for-A>`
   *
   *  For dependent Pi, we require the codomain to be a closed type
   *  (non-dependent arrow) to keep Phase 2 simple.
   */
  def apply_(fn: Term): TacticM[Unit] =
    for
      goalPair   <- TacticM.currentGoal
      (mv, goal)  = goalPair
      fnTpe      <- Bidirectional.infer(goal.ctx, fn) match
        case Right(t) => TacticM.pure(t)
        case Left(e)  => TacticM.fail(TacticError.TypeCheckFailed(e))
      result     <- Bidirectional.whnf(goal.ctx, fnTpe) match
        case Term.Pi(_, dom, cod) =>
          // The codomain after substituting the argument (not yet known).
          // For non-dependent cod, Var(0) does not appear; substitute Uni(0) as dummy.
          val codClosed = Subst.subst(Term.Uni(0), cod)
          val env       = buildEnv(goal.ctx)
          if Quote.convEqual(goal.ctx.size, env, codClosed, goal.target) then
            for
              argMv <- TacticM.addGoal(goal.ctx, dom)
              // Evidence: fn applied to the (future) argument
              // We record a placeholder; the argument metavar is argMv
              _     <- TacticM.solveGoalWith(mv, Term.App(fn, Term.Meta(argMv.id)))
            yield ()
          else
            TacticM.fail(TacticError.GoalMismatch(
              expected = goal.target.show,
              got      = codClosed.show,
            ))
        case nonPi =>
          TacticM.fail(TacticError.NotAFunction(fn.show))
    yield result

  // ---- helper ----

  private def buildEnv(ctx: Context): Env =
    (0 until ctx.size).toList.map(i => Semantic.freshVar(ctx.size - 1 - i))
