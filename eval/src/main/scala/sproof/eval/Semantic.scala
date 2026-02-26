package sproof.eval

import sproof.core.Term

/** Semantic domain for Normalization by Evaluation (NbE).
 *
 *  Closures are Scala functions (Semantic => Semantic), giving efficient
 *  evaluation without explicit substitution at each step.
 */
enum Semantic:
  /** λ abstraction: name, domain type, and a Scala closure for the body. */
  case SLam(name: String, tpe: Semantic, body: Semantic => Semantic)

  /** Dependent function type (Pi): domain and a closure for the codomain. */
  case SPi(name: String, dom: Semantic, cod: Semantic => Semantic)

  /** Universe at level l. */
  case SUni(level: Int)

  /** Constructor value: fully applied. */
  case SCon(name: String, indRef: String, args: List[Semantic])

  /** Stuck computation: a neutral head applied to a spine of arguments. */
  case SNeu(head: Neutral, spine: List[Semantic])

  def isNeu: Boolean = this match
    case SNeu(_, _) => true
    case _          => false

/** Neutral terms: computations stuck on a free variable or unresolved case. */
enum Neutral:
  /** A free variable identified by De Bruijn *level* (outermost = 0). */
  case NVar(level: Int)

  /** Application of a neutral function to a semantic argument. */
  case NApp(fn: Neutral, arg: Semantic)

  /** Pattern match on a neutral scrutinee. */
  case NMat(
    scrutinee: Neutral,
    cases: List[NeutralCase],
    returnTpe: Semantic => Semantic,
  )

  /** Fixed point applied to a neutral argument (needed for stuck recursion). */
  case NFix(name: String, body: Semantic => Semantic, arg: Neutral)

/** One case branch in a neutral match, represented as a closure over ctor args. */
case class NeutralCase(ctor: String, bindings: Int, body: List[Semantic] => Semantic)

object Semantic:
  val Type0: Semantic = SUni(0)
  val Type1: Semantic = SUni(1)

  /** Create a fresh semantic variable at the given De Bruijn level. */
  def freshVar(level: Int): Semantic = SNeu(Neutral.NVar(level), Nil)

  /** Apply a semantic function to a semantic argument (call-by-value). */
  def apply(fn: Semantic, arg: Semantic): Semantic = fn match
    case SLam(_, _, body) => body(arg)
    case SNeu(h, sp)      => SNeu(h, sp :+ arg)
    case other            => throw RuntimeException(s"Cannot apply non-function: $other")
