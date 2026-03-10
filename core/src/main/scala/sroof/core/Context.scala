package sroof.core

/** Typing context: an ordered list of variable bindings.
 *  Variables are referenced by De Bruijn index.
 *  The head of the list corresponds to index 0 (the most recently bound variable).
 */
final class Context private (
  val entries: List[Context.Entry],
  val size: Int,
):
  import Context.*

  /** Look up the type of variable at De Bruijn index i. */
  def lookup(i: Int): Option[Term] =
    if i < 0 || i >= size then None
    else entries.lift(i).map(e => Subst.shift(i + 1, e.tpe))

  /** Look up the definition of a let-bound variable at index i. */
  def lookupDef(i: Int): Option[Term] =
    if i < 0 || i >= size then None
    else entries.lift(i).flatMap {
      case Entry.Def(_, _, defn) => Some(Subst.shift(i + 1, defn))
      case _                     => None
    }

  /** Extend context with a new assumption x : T. */
  def extend(name: String, tpe: Term): Context =
    new Context(Entry.Assum(name, tpe) :: entries, size + 1)

  /** Extend context with a let-binding x : T = defn. */
  def extendDef(name: String, tpe: Term, defn: Term): Context =
    new Context(Entry.Def(name, tpe, defn) :: entries, size + 1)

  /** Name at De Bruijn index i (for error messages). */
  def nameAt(i: Int): String =
    entries.lift(i).map(_.name).getOrElse(s"#$i")

  def isEmpty: Boolean = entries.isEmpty

  override def toString: String =
    entries.zipWithIndex
      .map { case (e, i) => s"  $i: ${e.name} : ${e.tpe.show}" }
      .mkString("Context[\n", "\n", "\n]")

object Context:
  sealed trait Entry:
    def name: String
    def tpe: Term

  object Entry:
    case class Assum(name: String, tpe: Term) extends Entry
    case class Def(name: String, tpe: Term, defn: Term) extends Entry

  val empty: Context = new Context(Nil, 0)
