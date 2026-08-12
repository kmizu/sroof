package sroof.frontend

import sroof.core.{Context, DefEntry, GlobalEnv, Term}
import sroof.kernel.Kernel
import sroof.tactic.{Builtins, TacticError, TacticM}

/** Runs a resolved proof script and submits the result to the trusted kernel.
 *
 *  This is a frontend-neutral replacement for the `.sroof`-specific runner in
 *  `cli.Checker`: it depends on the IR, not on `syntax.SProof`/`syntax.STactic`.
 *
 *  The two-phase discipline of the legacy path is preserved exactly:
 *  tactics are untrusted **generators**, and a generated term is accepted only
 *  because `Kernel.verify` independently re-checks it.  A tactic returning
 *  success is never, on its own, grounds for accepting a theorem.  There is no
 *  `sorry`, no warning-only mode, and no fallback proof on this path.
 */
object ProofRunner:

  /** The name the tactic engine gives the induction hypothesis in the core
   *  context (`Builtins.buildFixCase` hard-codes it).  Scala pattern binders
   *  named this are rejected during extraction so the name can never be
   *  shadowed or ambiguous.
   */
  val IhBinderName: String = "ih"

  /** A theorem that has been proved and accepted by the kernel. */
  final case class VerifiedTheorem(name: String, entry: DefEntry, isSimp: Boolean)

  /** Prove one theorem and put the candidate term through the kernel.
   *
   *  @param theorem  the extracted theorem
   *  @param tenv     translation environment for the enclosing module
   *  @param env      global environment: inductives, definitions, and any
   *                  previously **verified** theorems
   */
  def verifyTheorem(
    theorem: ResolvedTheorem,
    tenv:    CoreTranslator.TranslationEnv,
    env:     GlobalEnv,
  ): Either[FrontendError, VerifiedTheorem] =
    given GlobalEnv = env
    for
      ctxAndTpes <- CoreTranslator.theoremContext(
                      theorem.params, tenv, theorem.name, theorem.span, theorem.typeParams)
      (ctx, paramTpes) = ctxAndTpes
      allParams   = theorem.typeParams ++ theorem.params
      // The goal is stated in the reversed parameter scope: the last parameter
      // is Var(0), matching the context built above.
      goal       <- CoreTranslator.translateProp(
                      theorem.goal, allParams.reverse.map(_.id), tenv, theorem.name)
      // The closed proposition, built before anything tries to prove it: a proof
      // of a statement that is not a proposition would mean nothing, and the
      // message for it should name that, not whatever the tactic engine hits
      // first while evaluating an ill-typed term.
      fullProp    = allParams.zip(paramTpes).foldRight(goal) { case ((p, t), cod) =>
                      Term.Pi(p.name, t, cod)
                    }
      _          <- wellFormedProp(fullProp, theorem)
      script     <- buildTactic(theorem.tactic, tenv, theorem.name, env)
      candidate  <- TacticM.prove(ctx, goal)(script).left.map { err =>
                      FrontendError.tacticError(theorem.name,
                        s"could not prove ${goal.show}: ${err.getMessage}", theorem.tactic.span)
                    }
      // Close over the parameters: the kernel is asked about the *closed*
      // proposition, so nothing is assumed about a free context.
      fullProof   = allParams.zip(paramTpes).foldRight(candidate) { case ((p, t), body) =>
                      Term.Lam(p.name, t, body)
                    }
      _          <- Kernel.verify(Context.empty, fullProof, fullProp).left.map { err =>
                      FrontendError.kernelError(theorem.name,
                        s"kernel rejected the generated proof: ${err.message}", theorem.span)
                    }
    yield VerifiedTheorem(theorem.name, DefEntry(theorem.name, fullProp, fullProof), theorem.isSimp)

  /** Check that a theorem's statement is a type before anyone proves it.
   *
   *  Nothing did this.  The kernel is asked whether the generated term has the
   *  claimed type; it is never asked whether the claim *is* a type, and the claim
   *  is produced by `CoreTranslator.translateProp`, which is inside the trust
   *  boundary.
   *
   *  Two details make that gap reachable rather than theoretical.
   *  `translateProp` discards the declared type and emits the **2-argument** `Eq`
   *  form, whose type slot is `Meta(-1)`; and `Kernel.check`'s `refl` case
   *  returns success on a `Meta` slot without checking the term has a type at
   *  all, on the recorded assumption that the caller already checked it.  For
   *  this caller the assumption did not hold, so a module could export a
   *  "verified theorem" whose statement was not a proposition — and later proofs
   *  cite verified theorems as lemmas.
   */
  private def wellFormedProp(
    prop:    Term,
    theorem: ResolvedTheorem,
  )(using GlobalEnv): Either[FrontendError, Unit] =
    import sroof.checker.{Bidirectional, TypeError}

    // `inferUniverse` answers `Right(0)` for an applied `Eq` **without looking at
    // the arguments** — the shape alone is taken as evidence. So asking it here
    // would accept exactly the statements this is meant to reject. What makes
    // `Eq A a b` a proposition is that both sides are typeable at one type, so
    // that is what gets checked: infer the left, check the right against it.
    def go(ctx: Context, t: Term): Either[TypeError, Unit] = t match
      case Term.Pi(name, dom, cod) =>
        for
          _ <- Bidirectional.inferUniverse(ctx, dom)
          _ <- go(ctx.extend(name, dom), cod)
        yield ()
      case _ =>
        sroof.tactic.Eq.extract(t) match
          case Some((_, lhs, rhs)) =>
            for
              tpe <- Bidirectional.infer(ctx, lhs)
              _   <- Bidirectional.check(ctx, rhs, tpe)
            yield ()
          case None =>
            Bidirectional.inferUniverse(ctx, t).map(_ => ())

    go(Context.empty, prop).left.map { err =>
      FrontendError.theoremError(theorem.name,
        s"statement is not a proposition: ${err.getMessage}", theorem.span)
    }

  /** Build the `TacticM` script for a resolved tactic. */
  private def buildTactic(
    tactic:  ResolvedTactic,
    tenv:    CoreTranslator.TranslationEnv,
    subject: String,
    env:     GlobalEnv,
  ): Either[FrontendError, TacticM[Unit]] =
    given GlobalEnv = env
    tactic match
      case ResolvedTactic.Trivial(_) =>
        Right(Builtins.trivial)

      case ResolvedTactic.Simplify(lemmas, _) =>
        resolveLemmaNames(lemmas, subject, env).map(Builtins.simplify)

      case ResolvedTactic.Rewrite(equations, _) =>
        resolveLemmaNames(equations, subject, env).map(Builtins.rewrite)

      case ResolvedTactic.Induction(_, targetName, cases, _) =>
        // `Builtins.induction` decides between a plain `Mat` and a `Fix`-wrapped
        // proof by comparing the binding count against the constructor arity:
        // one extra binding means "this branch wants an induction hypothesis".
        buildSplit(cases, tenv, subject, env) { caseSpecs =>
          Builtins.induction(targetName, caseSpecs)
        }

      case ResolvedTactic.InductionGeneralizing(_, targetName, generalizing, cases, _) =>
        buildSplit(cases, tenv, subject, env) { caseSpecs =>
          Builtins.induction(targetName, caseSpecs, generalizing.map(_._2))
        }

      case ResolvedTactic.ExactIh(at, span) =>
        Right(exactIh(at, tenv, subject))

      case ResolvedTactic.Have(lhs, rhs, name, proof, continue, _) =>
        for
          proofScript <- buildTactic(proof, tenv, subject, env)
          contScript  <- buildTactic(continue, tenv, subject, env)
        yield have(lhs, rhs, name, proofScript, contScript, tenv, subject)(using env)

      case ResolvedTactic.Cases(_, targetName, cases, _) =>
        // `cases` never requests a hypothesis, so the binding list is exactly the
        // constructor fields and `Builtins.cases` produces a plain `Mat`.
        buildSplit(cases, tenv, subject, env) { caseSpecs =>
          Builtins.cases(targetName, caseSpecs)
        }

  /** Close the goal with `ih` applied to the named values.
   *
   *  The proof context here is the one `Builtins` built for the branch, so its
   *  binders are addressed by name — the same way `Builtins` addresses them
   *  internally. The resulting term is a candidate like any other: if the
   *  hypothesis does not actually instantiate to the goal, the kernel rejects it.
   */
  /** Prove an intermediate claim, bind it, and continue.
   *
   *  Mirrors the `.sroof` path's `have`: the claim becomes a goal in its own
   *  right, its proof term is bound by a `Let`, and the continuation runs against
   *  the original goal in the extended context.  The claim's sides are resolved
   *  against the proof context, so `have` works inside an induction branch where
   *  the interesting terms mention the branch's binders.
   */
  private def have(
    lhsExpr: ResolvedExpr,
    rhsExpr: ResolvedExpr,
    name:    String,
    proof:   TacticM[Unit],
    continue: TacticM[Unit],
    tenv:    CoreTranslator.TranslationEnv,
    subject: String,
  )(using GlobalEnv): TacticM[Unit] =
    for
      goalPair  <- TacticM.currentGoal
      (mv, goal) = goalPair
      lhs       <- liftTranslation(lhsExpr, goal.ctx, tenv, subject)
      rhs       <- liftTranslation(rhsExpr, goal.ctx, tenv, subject)
      claim      = sroof.tactic.Eq.mkPropType(lhs, rhs)
      // Prove the claim as a separate goal, in the current context.
      claimTerm <- TacticM.liftEither(
                     TacticM.prove(goal.ctx, claim)(proof).left.map { err =>
                       TacticError.Custom(s"have: could not prove ${claim.show}: ${err.getMessage}")
                     })
      newCtx     = goal.ctx.extend(name, claim)
      newTarget  = sroof.core.Subst.shift(1, goal.target)
      contMv    <- TacticM.addGoal(newCtx, newTarget)
      _         <- TacticM.solveGoalWith(mv, Term.Let(name, claim, claimTerm, Term.Meta(contMv.id)))
      _         <- continue
    yield ()

  private def liftTranslation(
    e:       ResolvedExpr,
    ctx:     Context,
    tenv:    CoreTranslator.TranslationEnv,
    subject: String,
  ): TacticM[Term] =
    CoreTranslator.translateInProofContext(e, ctx, tenv, subject) match
      case Right(t)  => TacticM.pure(t)
      case Left(err) => TacticM.fail[Term](TacticError.Custom(err.message))

  private def exactIh(
    at:      List[ResolvedExpr],
    tenv:    CoreTranslator.TranslationEnv,
    subject: String,
  ): TacticM[Unit] =
    for
      goalPair  <- TacticM.currentGoal
      (mv, goal) = goalPair
      ihIdx     <- goal.ctx.entries.indexWhere(_.name == IhBinderName) match
                     case -1 => TacticM.fail[Int](TacticError.Custom(
                       "exactIh: no induction hypothesis is in scope here"))
                     case i  => TacticM.pure(i)
      args      <- at.foldLeft(TacticM.pure(List.empty[Term])) { (acc, e) =>
                     acc.flatMap { done =>
                       CoreTranslator.translateInProofContext(e, goal.ctx, tenv, subject) match
                         case Right(t)  => TacticM.pure(done :+ t)
                         case Left(err) => TacticM.fail[List[Term]](TacticError.Custom(err.message))
                     }
                   }
      // The result is a candidate like any other: if the hypothesis does not
      // instantiate to the goal, the kernel rejects the whole theorem.
      term       = args.foldLeft(Term.Var(ihIdx): Term)(Term.App.apply)
      _         <- TacticM.solveGoalWith(mv, term)
    yield ()

  /** Build a constructor-splitting tactic followed by its branch tactics.
   *
   *  Shared by `induction` and `cases`: both generate one subgoal per
   *  constructor, in constructor order, and then run each branch against its own
   *  subgoal.
   */
  private def buildSplit(
    cases:   List[ResolvedTacticCase],
    tenv:    CoreTranslator.TranslationEnv,
    subject: String,
    env:     GlobalEnv,
  )(split: List[(String, List[String])] => TacticM[Unit]): Either[FrontendError, TacticM[Unit]] =
    val caseSpecs = cases.map { c =>
      val bindings = c.binders.map(_.name) ++ (if c.usesIh then List(IhBinderName) else Nil)
      (c.ctorName, bindings)
    }
    cases
      .foldLeft[Either[FrontendError, List[TacticM[Unit]]]](Right(Nil)) { (acc, c) =>
        for
          done <- acc
          t    <- buildTactic(c.tactic, tenv, subject, env)
        yield done :+ t
      }
      .map { branches =>
        val runBranches = branches.foldLeft(TacticM.pure(()))((acc, b) => acc.flatMap(_ => b))
        split(caseSpecs).flatMap(_ => runBranches)
      }

  private def resolveLemmaNames(
    lemmas:  List[ResolvedLemmaRef],
    subject: String,
    env:     GlobalEnv,
  ): Either[FrontendError, List[String]] =
    lemmas.foldLeft[Either[FrontendError, List[String]]](Right(Nil)) { (acc, lemma) =>
      for
        names <- acc
        name  <- lemmaName(lemma, subject, env)
      yield names :+ name
    }

  /** Resolve a `simplify` lemma to the name the tactic engine looks up. */
  private def lemmaName(
    lemma:   ResolvedLemmaRef,
    subject: String,
    env:     GlobalEnv,
  ): Either[FrontendError, String] =
    lemma match
      case ResolvedLemmaRef.InductionHypothesis(_, _, _) =>
        Right(IhBinderName)
      case ResolvedLemmaRef.LocalHypothesis(name, _) =>
        // Bound by an enclosing `have`, so it lives in the proof context under
        // this name; the tactic engine resolves it there.
        Right(name)
      case ResolvedLemmaRef.Theorem(_, name, span) =>
        // Only theorems already accepted by the kernel are in `env`, so a
        // forward reference or an unproved theorem fails here rather than
        // silently contributing to a later proof.
        if env.lookupDef(name).isDefined then Right(name)
        else Left(FrontendError.tacticError(subject,
          s"lemma '$name' is not a theorem that has already been verified in this module", span))
