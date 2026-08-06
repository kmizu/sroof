package sroof.frontend

import sroof.core.GlobalEnv

/** Verifies one `@proofModule` end to end.
 *
 *  Order matters and is fixed here:
 *
 *  1. enums become inductive types (strict positivity checked);
 *  2. definitions are scheduled by dependency and translated (termination
 *     checked), each becoming available to the next;
 *  3. theorems are proved in source order, and a theorem enters the environment
 *     — and `simpSet` — only **after** the kernel has accepted its proof.
 *
 *  Step 3 is what keeps proof reuse honest: an unproved or rejected theorem can
 *  never be used as a lemma by a later one, because it never reaches `env`.
 */
object ModuleVerifier:

  /** What a successful verification produced, for tests and diagnostics. */
  final case class VerifiedModule(
    name:     String,
    env:      GlobalEnv,
    theorems: List[ProofRunner.VerifiedTheorem],
  )

  /** Verify a module, stopping at the first error.
   *
   *  Errors are returned, never thrown, and never swallowed: there is no
   *  catch-all branch that yields an empty theorem set on failure.
   */
  def verify(module: ResolvedModule): Either[FrontendError, VerifiedModule] =
    for
      indDefs <- module.inductives.foldLeft[Either[FrontendError, List[sroof.core.IndDef]]](Right(Nil)) {
                   (acc, ind) =>
                     for
                       done <- acc
                       d    <- CoreTranslator.translateInductive(ind)
                     yield done :+ d
                 }
      envWithInds = indDefs.foldLeft(GlobalEnv.empty)(_.addInd(_))
      tenv0       = CoreTranslator.TranslationEnv(module)
      ordered    <- CoreTranslator.orderDefinitions(module)
      translated <- ordered.foldLeft[Either[FrontendError, (CoreTranslator.TranslationEnv, GlobalEnv)]](
                      Right((tenv0, envWithInds))
                    ) { (acc, rd) =>
                      for
                        state <- acc
                        (tenv, env) = state
                        entry <- CoreTranslator.translateDef(rd, tenv)
                      yield (tenv.copy(defs = tenv.defs + (rd.id -> entry)), env.addDef(entry))
                    }
      (tenv, envWithDefs) = translated
      proved     <- module.theorems.foldLeft[Either[FrontendError, (GlobalEnv, List[ProofRunner.VerifiedTheorem])]](
                      Right((envWithDefs, Nil))
                    ) { (acc, th) =>
                      for
                        state <- acc
                        (env, done) = state
                        verified <- ProofRunner.verifyTheorem(th, tenv, env)
                        // Only now — after the kernel accepted it — does the
                        // theorem become visible to later proofs.
                        nextEnv0  = env.addDef(verified.entry)
                        nextEnv   = if verified.isSimp then nextEnv0.addToSimpSet(verified.name) else nextEnv0
                      yield (nextEnv, done :+ verified)
                    }
      (finalEnv, theorems) = proved
    yield VerifiedModule(module.name, finalEnv, theorems)
