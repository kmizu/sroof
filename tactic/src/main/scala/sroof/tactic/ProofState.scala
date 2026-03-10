package sroof.tactic

import sroof.core.{Term, Context}

/** An opaque identifier for a metavariable (proof hole). */
opaque type MetaVar = Int

object MetaVar:
  def apply(i: Int): MetaVar = i
  extension (mv: MetaVar)
    def id: Int = mv

/** A proof obligation: prove `target` in the given `ctx`. */
case class Goal(ctx: Context, target: Term)

/** The complete proof state at any point during tactic execution.
 *
 *  @param goals    Remaining proof obligations (ordered; first = current goal).
 *  @param evidence Filled proof holes: MetaVar → Term.
 *  @param nextMeta Counter for fresh MetaVar generation.
 */
case class ProofState(
  goals:    List[(MetaVar, Goal)],
  evidence: Map[MetaVar, Term],
  nextMeta: Int,
)

object ProofState:
  val empty: ProofState = ProofState(Nil, Map.empty, 0)
