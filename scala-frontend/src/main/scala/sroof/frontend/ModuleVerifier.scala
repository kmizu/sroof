package sroof.frontend

import sroof.core.{Context, DefEntry, GlobalEnv}
import sroof.kernel.Kernel

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
    // The promise above ("returned, never thrown") was not kept. `Eval` throws on
    // a term it cannot reduce — an unbound index, a match with no branch for the
    // scrutinee's constructor — and every such term here comes from an ill-typed
    // core term, which is precisely what a bridge bug produces. On the `.sroof`
    // path each entry to evaluation is wrapped (`Checker.executeProof`,
    // `Bidirectional.whnf`, `Kernel.check`); on this path nothing was, so the
    // exception left `verify` and reached the compiler as a crash with no source
    // position instead of an error on the offending theorem.
    //
    // Rejection-safe by construction: the handler produces a `Left`, so an
    // exception can only lose a proof, never manufacture one.
    try verifyUnguarded(module)
    catch
      case scala.util.control.NonFatal(e) =>
        Left(FrontendError.moduleError(FrontendStage.KernelVerification,
          s"verification of '${module.name}' failed while evaluating a term: " +
          s"${Option(e.getMessage).getOrElse(e.getClass.getName)}", module.span))

  private def verifyUnguarded(module: ResolvedModule): Either[FrontendError, VerifiedModule] =
    for
      // The environment grows as inductives are translated, in declaration
      // order: the positivity check for inductive k needs the constructors of
      // the inductives it nests inside, which must therefore come before it.
      envWithInds <- module.inductives.foldLeft[Either[FrontendError, GlobalEnv]](
                       Right(GlobalEnv.empty)
                     ) { (acc, ind) =>
                       for
                         genv <- acc
                         d    <- CoreTranslator.translateInductive(ind)(using genv)
                       yield genv.addInd(d)
                     }
      tenv0       = CoreTranslator.TranslationEnv(module)
      ordered    <- CoreTranslator.orderDefinitions(module)
      translated <- ordered.foldLeft[Either[FrontendError, (CoreTranslator.TranslationEnv, GlobalEnv)]](
                      Right((tenv0, envWithInds))
                    ) { (acc, rd) =>
                      for
                        state <- acc
                        (tenv, env) = state
                        entry <- CoreTranslator.translateDef(rd, tenv)
                        _     <- verifyDefBody(entry, rd.name, rd.span)(using env)
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

  /** Put a translated definition's body through the kernel, against its own
   *  declared type.
   *
   *  Nothing else does this.  `translateDef` checks termination and then trusts
   *  itself: the body is produced by `CoreTranslator`, which is *inside* the
   *  trust boundary, so a mistranslation that yields an ill-typed core term had
   *  no one to catch it.  The Scala typer does not help here — it checks the
   *  Scala program, and the question is whether the core term still means the
   *  same thing.  The `.sroof` frontend closed this exact gap in v0.14
   *  (`Checker.checkDefBodies`); this is the second frontend saying the same
   *  thing, so a definition cannot say one thing and mean another on either
   *  path.
   *
   *  Calls to other definitions are inlined (core `Term` has no
   *  global-reference node), so the body is closed and `Context.empty` is the
   *  right context.  The environment carries the inductives it mentions.
   */
  private def verifyDefBody(
    entry: DefEntry,
    name:  String,
    span:  SourceSpan,
  )(using GlobalEnv): Either[FrontendError, Unit] =
    Kernel.verify(Context.empty, entry.body, entry.tpe).left.map { err =>
      FrontendError.kernelError(name,
        s"definition does not match its declared type: ${err.message}", span)
    }
