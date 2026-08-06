package sroof.frontend

/** The stage a failure came from.  Reported to the user so a diagnostic says
 *  *where in the pipeline* something went wrong, not just what.
 */
enum FrontendStage:
  case EnumTranslation
  case DefinitionTranslation
  case TheoremExtraction
  case TacticExecution
  case KernelVerification

  def label: String = this match
    case EnumTranslation       => "enum translation"
    case DefinitionTranslation => "verified definition translation"
    case TheoremExtraction     => "theorem extraction"
    case TacticExecution       => "tactic execution"
    case KernelVerification    => "kernel verification"

/** A source-positioned frontend failure.
 *
 *  Position-neutral by construction: the span travels with the error so the
 *  compiler-specific layer can turn it back into a real compiler position
 *  without this module knowing anything about dotc.
 *
 *  `subject` is the friendly name of the theorem or definition involved, so a
 *  message can read "theorem plusZeroRight: ..." rather than pointing at an
 *  anonymous tree.
 */
final case class FrontendError(
  stage:   FrontendStage,
  subject: String,
  message: String,
  span:    SourceSpan,
):
  /** The user-facing one-liner, without the `[sroof]` prefix the plugin adds. */
  def render: String =
    if subject.isEmpty then s"${stage.label}: $message"
    else s"$subject: $message"

/** Constructors take the *bare* name of the enum/definition/theorem and add the
 *  declaration kind, so every sroof diagnostic reads the same way:
 *  `theorem plusZeroRight: ...`, `verified definition plus: ...`.
 */
object FrontendError:
  def enumError(name: String, message: String, span: SourceSpan): FrontendError =
    FrontendError(FrontendStage.EnumTranslation, s"enum $name", message, span)

  def defError(name: String, message: String, span: SourceSpan): FrontendError =
    FrontendError(FrontendStage.DefinitionTranslation, s"verified definition $name", message, span)

  def theoremError(name: String, message: String, span: SourceSpan): FrontendError =
    FrontendError(FrontendStage.TheoremExtraction, s"theorem $name", message, span)

  def tacticError(name: String, message: String, span: SourceSpan): FrontendError =
    FrontendError(FrontendStage.TacticExecution, s"theorem $name", message, span)

  def kernelError(name: String, message: String, span: SourceSpan): FrontendError =
    FrontendError(FrontendStage.KernelVerification, s"theorem $name", message, span)

  /** For failures that are not attributable to one named declaration. */
  def moduleError(stage: FrontendStage, message: String, span: SourceSpan): FrontendError =
    FrontendError(stage, "", message, span)
