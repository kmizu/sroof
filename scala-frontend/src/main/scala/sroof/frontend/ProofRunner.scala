package sroof.frontend

import sroof.core.{Context, DefEntry, GlobalEnv, Term}
import sroof.kernel.Kernel
import sroof.tactic.{Builtins, TacticM}

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
      ctxAndTpes <- CoreTranslator.theoremContext(theorem.params, tenv, theorem.name, theorem.span)
      (ctx, paramTpes) = ctxAndTpes
      // The goal is stated in the reversed parameter scope: the last parameter
      // is Var(0), matching the context built above.
      goal       <- CoreTranslator.translateProp(
                      theorem.goal, theorem.params.reverse.map(_.id), tenv, theorem.name)
      script     <- buildTactic(theorem.tactic, tenv, theorem.name, env)
      candidate  <- TacticM.prove(ctx, goal)(script).left.map { err =>
                      FrontendError.tacticError(theorem.name,
                        s"could not prove ${goal.show}: ${err.getMessage}", theorem.tactic.span)
                    }
      // Close over the parameters: the kernel is asked about the *closed*
      // proposition, so nothing is assumed about a free context.
      fullProof   = theorem.params.zip(paramTpes).foldRight(candidate) { case ((p, t), body) =>
                      Term.Lam(p.name, t, body)
                    }
      fullProp    = theorem.params.zip(paramTpes).foldRight(goal) { case ((p, t), cod) =>
                      Term.Pi(p.name, t, cod)
                    }
      _          <- Kernel.verify(Context.empty, fullProof, fullProp).left.map { err =>
                      FrontendError.kernelError(theorem.name,
                        s"kernel rejected the generated proof: ${err.message}", theorem.span)
                    }
    yield VerifiedTheorem(theorem.name, DefEntry(theorem.name, fullProp, fullProof), theorem.isSimp)

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

      case ResolvedTactic.Cases(_, targetName, cases, _) =>
        // `cases` never requests a hypothesis, so the binding list is exactly the
        // constructor fields and `Builtins.cases` produces a plain `Mat`.
        buildSplit(cases, tenv, subject, env) { caseSpecs =>
          Builtins.cases(targetName, caseSpecs)
        }

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
      case ResolvedLemmaRef.Theorem(_, name, span) =>
        // Only theorems already accepted by the kernel are in `env`, so a
        // forward reference or an unproved theorem fails here rather than
        // silently contributing to a later proof.
        if env.lookupDef(name).isDefined then Right(name)
        else Left(FrontendError.tacticError(subject,
          s"lemma '$name' is not a theorem that has already been verified in this module", span))
