package sroof.kernel

import sroof.core.{Term, Context, GlobalEnv, TerminationChecker}
import sroof.checker.{Bidirectional, TypeError}
import sroof.eval.{Quote, EnvBuilder}
import sroof.tactic.Eq

/** The trusted kernel: the sole source of proof validity in sroof.
 *
 *  Every completed proof MUST pass through `Kernel.check` before being
 *  accepted.  Tactics (TacticM, Builtins) are NOT trusted — they are
 *  proof-term generators.  The kernel independently re-verifies that the
 *  generated term has the claimed type.
 *
 *  Size target: < 100 lines of logic (this is the Trusted Computing Base).
 *
 *  "仕様を書いて証明プログラムが型エラーになれば失敗が明確":
 *  This object is the type-checker that enforces that invariant.
 */
object Kernel:

  /** Typed errors returned by [[verify]].
   *
   *  `verify` is the stable final-verification API for callers outside the
   *  kernel package.  It wraps lower-level checker errors while preserving
   *  the original details.
   */
  enum VerificationError:
    case TypeCheckFailed(cause: TypeError)

    def message: String = this match
      case TypeCheckFailed(cause) => cause.getMessage

  /** Check that `proof` has type `claimedType` in context `ctx`.
   *
   *  Returns Right(()) on success, Left(TypeError) on failure.
   *  Special-cases the Eq/refl encoding used in Phase 2.
   */
  /** Every `Fix` in an accepted proof must be structurally decreasing.
   *
   *  The bidirectional checker types `Fix(f, T, body)` with `f : T` assumed in
   *  scope — sound only if the recursion is well-founded, which types alone
   *  cannot see: `Fix("pf", P, Var(0))` is a well-typed "proof" of any `P` by
   *  appeal to itself, and without this check [[verify]] accepted it (measured;
   *  see `KernelSuite`). The front ends run the termination check on `def`
   *  bodies, but proof terms come from the tactic layer, which is *untrusted* —
   *  so the kernel, as sole arbiter, has to run it here. Nested `Fix` nodes
   *  each get their own check: `TerminationChecker.check` guards one fixpoint's
   *  own self-reference, not those of fixpoints inside it.
   */
  private def guardFixes(t: Term)(using env: GlobalEnv): Either[TypeError, Unit] = t match
    case fix @ Term.Fix(_, tp, body) =>
      TerminationChecker.check(fix) match
        case Left(msg) => Left(TypeError.Custom(s"Kernel guard: $msg"))
        case Right(()) =>
          for
            _ <- guardFixes(tp)
            _ <- guardFixes(body)
          yield ()
    case Term.App(fn, arg) =>
      for
        _ <- guardFixes(fn)
        _ <- guardFixes(arg)
      yield ()
    case Term.Lam(_, tp, body) =>
      for
        _ <- guardFixes(tp)
        _ <- guardFixes(body)
      yield ()
    case Term.Pi(_, dom, cod) =>
      for
        _ <- guardFixes(dom)
        _ <- guardFixes(cod)
      yield ()
    case Term.Let(_, tp, defn, body) =>
      for
        _ <- guardFixes(tp)
        _ <- guardFixes(defn)
        _ <- guardFixes(body)
      yield ()
    case Term.Con(_, _, args) =>
      args.foldLeft[Either[TypeError, Unit]](Right(())) { (acc, a) =>
        acc.flatMap(_ => guardFixes(a))
      }
    case Term.Mat(s, cases, rt) =>
      for
        _ <- guardFixes(s)
        _ <- guardFixes(rt)
        _ <- cases.foldLeft[Either[TypeError, Unit]](Right(())) { (acc, c) =>
               acc.flatMap(_ => guardFixes(c.body))
             }
      yield ()
    case Term.Var(_) | Term.Uni(_) | Term.Ind(_, _, _) | Term.Meta(_) =>
      Right(())

  def check(ctx: Context, proof: Term, claimedType: Term)(using env: GlobalEnv): Either[TypeError, Unit] =
    for
      _ <- guardFixes(proof)
      _ <- checkTyped(ctx, proof, claimedType)
    yield ()

  private def checkTyped(ctx: Context, proof: Term, claimedType: Term)(using env: GlobalEnv): Either[TypeError, Unit] =
    // Special case: refl(a) must have type Eq T a a.
    // We do NOT whnf the claimed type here because our NbE evaluation of Ind("Eq",...)
    // loses the constructor name — use the raw syntactic structure of claimedType instead.
    (proof, Eq.extract(claimedType)) match
      case (Term.Con("refl", "Eq", List(a)), Some(triple)) =>
        val (tpe, lhs, rhs) = triple
        val env = EnvBuilder.fromContext(ctx)
        // refl(a) : Eq T a a  iff  a ≡ lhs ≡ rhs (definitionally)
        // A term the evaluator cannot reduce is not equal to anything: an
        // evaluator exception is a rejection, never an escape.
        val reflOk =
          try Quote.convEqual(ctx.size, env, a, lhs) && Quote.convEqual(ctx.size, env, lhs, rhs)
          catch case scala.util.control.NonFatal(_) => false
        if reflOk then
          // Also verify a : T, but skip when T is Meta(-1) (unknown, from 2-arg Eq form).
          // In that case, a was already type-checked by the bidirectional checker.
          tpe match
            case Term.Meta(_) => Right(())
            case _            => Bidirectional.check(ctx, a, tpe)
        else
          Left(TypeError.TypeMismatch(claimedType, proof, proof, ctx))

      case _ =>
        // General case: delegate to the bidirectional checker
        Bidirectional.check(ctx, proof, claimedType)

  /** Final kernel verification API.
   *
   *  Call this API for the final accept/reject decision of a proof term.
   *  It performs independent trusted-kernel checking and returns typed
   *  verification errors.
   */
  def verify(ctx: Context, proof: Term, claimedType: Term)(using env: GlobalEnv): Either[VerificationError, Unit] =
    check(ctx, proof, claimedType).left.map(VerificationError.TypeCheckFailed.apply)

  /** Infer the type of a term; re-export for convenience. */
  def infer(ctx: Context, term: Term)(using env: GlobalEnv): Either[TypeError, Term] =
    Bidirectional.infer(ctx, term)

