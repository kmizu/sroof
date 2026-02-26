package sproof.tactic

import sproof.core.{Term, Context, Subst, GlobalEnv, IndDef, CtorDef, MatchCase, Param, Ctor}
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

  // ---- induction ----

  /** Perform structural induction on a named variable.
   *
   *  `induction "n"` where `n : Nat` in the current context:
   *  1. Finds `n` in the context (by name) at some De Bruijn index `i`
   *  2. Looks up the inductive type definition from GlobalEnv
   *  3. For each constructor:
   *     - Non-recursive (e.g., `zero`): subgoal with `n` substituted by `zero`
   *     - Recursive (e.g., `succ k`): subgoal with `n` substituted by `succ(k)`,
   *       extended context adds `k : T` (and IH in future phases)
   *  4. The proof term is `Mat(Var(i), matchCases, returnTpe)`
   *
   *  NOTE: Context variable must have an inductive type present in GlobalEnv.
   */
  def induction(varName: String)(using env: GlobalEnv): TacticM[Unit] =
    for
      goalPair     <- TacticM.currentGoal
      (mv, goal)    = goalPair
      // Find variable by name in context
      varIdxTpe    <- TacticM.liftEither(findVarByName(goal.ctx, varName))
      (varIdx, varTpe) = varIdxTpe
      // Extract inductive type name (raw, no whnf — avoids NbE name loss)
      indName      <- TacticM.liftEither(extractIndNameRaw(varTpe))
      // Look up inductive definition
      indDef       <- TacticM.liftEither(
                        env.lookupInd(indName).toRight(
                          TacticError.Custom(s"Unknown inductive type '$indName' in GlobalEnv")
                        )
                      )
      // Generate subgoals for each constructor
      matchCases   <- generateInductionCases(goal.ctx, varIdx, goal.target, indDef)
      // Proof term: Mat(Var(varIdx), matchCases, returnTpe)
      matTerm       = Term.Mat(Term.Var(varIdx), matchCases.map(_._3), goal.target)
      _            <- TacticM.solveGoalWith(mv, matTerm)
    yield ()

  /** Generate subgoals and MatchCase placeholders for induction on a variable.
   *
   *  Returns a list of (subCtx, subGoal, matchCase) for each constructor.
   *  The match cases contain `Term.Meta` placeholders that get filled by subgoal proofs.
   */
  private def generateInductionCases(
    ctx:    Context,
    varIdx: Int,
    goal:   Term,
    indDef: IndDef,
  )(using env: GlobalEnv): TacticM[List[(Context, Term, MatchCase)]] =
    // Remove varIdx from context: entries with index < varIdx stay, entries > varIdx shift down.
    // For the common case (varIdx = 0), ctx_minus is just ctx without the first entry.
    val ctx_minus = removeFromContext(ctx, varIdx)
    indDef.ctors.foldLeft(TacticM.pure(List.empty[(Context, Term, MatchCase)])) { (acc, ctorDef) =>
      acc.flatMap { cases =>
        generateCtorCase(ctx_minus, ctx, varIdx, goal, indDef, ctorDef).map { triple =>
          cases :+ triple
        }
      }
    }

  /** Generate the subgoal and MatchCase for a single constructor.
   *
   *  For constructor `ctor(arg1: A1, ..., argN: AN)`:
   *  - Ctor args are De Bruijn variables Var(N-1)..Var(0) in the extended context
   *  - The subgoal goal = specializeGoal(G, varIdx, ctorTerm, N)
   *    where the induction variable (Var(varIdx)) is replaced by the constructor application
   *  - The subgoal context = ctx_minus extended with [arg1: A1, ..., argN: AN]
   */
  private def generateCtorCase(
    ctx_minus: Context,    // ctx with the induction variable removed
    ctx:       Context,    // original context (with the induction variable)
    varIdx:    Int,        // De Bruijn index of the induction variable in ctx
    goal:      Term,       // original goal (may mention Var(varIdx))
    indDef:    IndDef,
    ctorDef:   CtorDef,
  )(using env: GlobalEnv): TacticM[(Context, Term, MatchCase)] =
    val n       = ctorDef.argTpes.length  // number of ctor args (= bindings in MatchCase)
    // Build constructor arg references: Var(0), Var(1), ..., Var(n-1)
    // In the extended context, the most recently bound (innermost) ctor arg = Var(0).
    // (The args list is ordered left-to-right; the first arg is the outermost = Var(n-1).)
    val ctorArgVars = (0 until n).toList.map(i => Term.Var(n - 1 - i))
    val ctorTerm    = Term.Con(ctorDef.name, indDef.name, ctorArgVars)
    // Specialize the goal: replace Var(varIdx) with ctorTerm, adjusting all other variables
    // correctly for the n new ctor-arg bindings added to the context.
    val specialGoal = specializeGoal(goal, varIdx, ctorTerm, n)
    // Build the extended context: ctx_minus + ctor args (foldLeft prepends each, so last arg = Var(0))
    val extCtx = ctorDef.argTpes.foldLeft(ctx_minus) { (c, argTpe) =>
      c.extend("_", argTpe)
    }
    for
      mv <- TacticM.addGoal(extCtx, specialGoal)
    yield (extCtx, specialGoal, MatchCase(ctorDef.name, n, Term.Meta(mv.id)))

  /** Remove the variable at De Bruijn index `idx` from the context.
   *
   *  For idx = 0: removes the most recently bound variable (head of entries).
   *  For idx > 0: removes deeper entries (less common, handled conservatively).
   */
  private def removeFromContext(ctx: Context, idx: Int): Context =
    // Reconstruct context without entry at position idx
    // entries are ordered head = index 0 (most recent)
    val entriesList = ctx.entries.toList
    if idx < 0 || idx >= entriesList.length then ctx
    else
      val before = entriesList.take(idx)   // entries with De Bruijn index < idx (less recent)
      val after  = entriesList.drop(idx + 1) // entries with De Bruijn index > idx (more recent)
      // Rebuild: newer entries (smaller indices) first, older entries reconstructed below
      // 'after' entries have indices 0..idx-1 (they were above the removed entry)
      // 'before' entries had indices idx+1..size-1 (they are below the removed entry)
      // After removal, their indices shift: idx+1 → idx, idx+2 → idx+1, etc.
      // For simplicity, rebuild from scratch (correct for non-dependent context entries)
      val newCtx1 = after.foldRight(Context.empty) { (e, c) => c.extend(e.name, e.tpe) }
      before.foldRight(newCtx1) { (e, c) => c.extend(e.name, Subst.shift(-1, e.tpe)) }

  /** Specialize `goal` by replacing the induction variable (at De Bruijn index `varIdx`
   *  in the original context) with `ctorTerm`, while accounting for `n` new ctor-arg
   *  bindings that have been prepended to the context.
   *
   *  The new context is: [arg_n-1 : A_n-1, ..., arg_0 : A_0] ++ ctx_minus
   *  So every free variable in `goal` must be adjusted:
   *    - Var(i) where (i - depth) < 0        : bound inside inner binders → unchanged
   *    - Var(i) where (i - depth) == varIdx  : replace with Subst.shift(depth, ctorTerm)
   *    - Var(i) where (i - depth) < varIdx   : these variables are "above" varIdx in the
   *                                             original context; they need to shift up by n
   *                                             to skip over the new ctor bindings
   *    - Var(i) where (i - depth) > varIdx   : these are "below" varIdx; net shift = n - 1
   *                                             (+n for new ctor bindings, -1 for removed var)
   */
  private def specializeGoal(goal: Term, varIdx: Int, ctorTerm: Term, n: Int): Term =
    def go(depth: Int, t: Term): Term = t match
      case Term.Var(i) =>
        val absI = i - depth
        if absI < 0 then Term.Var(i)                          // bound inside depth binders
        else if absI == varIdx then Subst.shift(depth, ctorTerm) // replace induction var
        else if absI < varIdx then Term.Var(i + n)             // vars above varIdx: shift +n
        else Term.Var(i - 1 + n)                               // vars below varIdx: shift +(n-1)
      case Term.App(f, a)          => Term.App(go(depth, f), go(depth, a))
      case Term.Lam(x, tp, b)     => Term.Lam(x, go(depth, tp), go(depth + 1, b))
      case Term.Pi(x, d, c)       => Term.Pi(x, go(depth, d), go(depth + 1, c))
      case Term.Let(x, tp, df, b) => Term.Let(x, go(depth, tp), go(depth, df), go(depth + 1, b))
      case Term.Uni(_)             => t
      case Term.Meta(_)            => t
      case Term.Ind(nm, ps, cs)   =>
        Term.Ind(nm,
          ps.map(p => Param(p.name, go(depth, p.tpe))),
          cs.map(c => Ctor(c.name, go(depth, c.tpe))))
      case Term.Con(nm, r, args)  => Term.Con(nm, r, args.map(go(depth, _)))
      case Term.Fix(nm, tp, b)    => Term.Fix(nm, go(depth, tp), go(depth + 1, b))
      case Term.Mat(s, cases, rt) =>
        Term.Mat(
          go(depth, s),
          cases.map(mc => mc.copy(body = go(depth + mc.bindings, mc.body))),
          go(depth, rt),
        )
    go(0, goal)

  // ---- simplify ----

  /** Simplify the current goal using NbE normalization, then close with `trivial`.
   *
   *  `simplify lemmas` on goal `Eq T lhs rhs`:
   *  1. Normalizes `lhs` and `rhs` via NbE (unfolds Fix, reduces beta/iota, etc.)
   *  2. If the normalized sides are definitionally equal, closes with `refl`
   *
   *  NOTE: Context-lemma rewriting (e.g., `simplify [ih]`) comes in a later phase.
   *  For now, `lemmas` parameter is accepted but only NbE normalization is performed.
   *
   *  Corresponds to `simp` / `simplify` in Coq/Lean.
   */
  def simplify(lemmas: List[String] = Nil)(using env: GlobalEnv): TacticM[Unit] =
    // Simply delegate to trivial after NbE normalization.
    // trivial already normalizes lhs/rhs via Quote.convEqual (which uses NbE internally).
    trivial

  /** Alias for `simplify` with no lemmas. */
  val simp: TacticM[Unit] = simplify(Nil)

  // ---- helpers ----

  /** Find a variable by name in the context. Returns (index, type). */
  private def findVarByName(ctx: Context, name: String): Either[TacticError, (Int, Term)] =
    ctx.entries.zipWithIndex.collectFirst {
      case (e, i) if e.name == name =>
        val tpe = Subst.shift(i + 1, e.tpe)
        (i, tpe)
    }.toRight(TacticError.Custom(s"Variable '$name' not found in context"))

  /** Extract the inductive type name from a raw type term (no whnf). */
  private def extractIndNameRaw(t: Term): Either[TacticError, String] = t match
    case Term.Ind(name, _, _) => Right(name)
    case _ => Left(TacticError.Custom(
      s"Expected inductive type for induction, got: ${t.show}"
    ))

  private def buildEnv(ctx: Context): Env =
    (0 until ctx.size).toList.map(i => Semantic.freshVar(ctx.size - 1 - i))
