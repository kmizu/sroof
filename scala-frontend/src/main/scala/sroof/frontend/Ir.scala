package sroof.frontend

/** The resolved frontend IR.
 *
 *  This is the boundary between "what the Scala compiler saw" and "what sroof
 *  reasons about".  It is deliberately **independent of `dotty.tools.dotc`**:
 *  nothing here may reference a compiler type, so the translation and proof
 *  layers can be unit-tested and ported to a future Scala version without
 *  touching the compiler-specific extraction code.
 *
 *  Two rules shape the ADT:
 *
 *  1. Every reference carries a [[SymbolId]] — a canonical, compiler-resolved
 *     identity.  Human-readable names ride along for diagnostics and for core
 *     binder labels, but they are never used to decide what something *is*.
 *  2. There is no `Unknown`/`Other` escape hatch.  A construct the extractor
 *     cannot resolve must become a [[FrontendError]], never an IR node.
 */

/** A canonical, collision-resistant identity for a compiler symbol.
 *
 *  Built by the plugin from the fully qualified symbol name plus, where
 *  overloading makes that ambiguous, a stable signature.  Never parsed or
 *  pattern-matched on — only compared.
 */
final case class SymbolId(value: String)

/** A source range, in the compiler's original coordinates. */
final case class SourceSpan(path: String, start: Int, end: Int, line: Int, column: Int):
  /** `file.scala:12` — for diagnostics that cannot carry a real position. */
  def display: String = s"$path:$line"

object SourceSpan:
  /** For IR built by tests or synthesised internally, with no source behind it. */
  val synthetic: SourceSpan = SourceSpan("<synthetic>", 0, 0, 0, 0)

/** Anything that can point back at the source the user wrote.
 *
 *  Declared abstract so that enum cases can satisfy it with an ordinary `span`
 *  parameter, which is what keeps positions attached to every node without
 *  duplicating an accessor per case.
 */
sealed trait Spanned:
  def span: SourceSpan

/** Anything carrying a human-readable name, used only for diagnostics. */
sealed trait Named:
  def name: String

/** A type in the supported subset.
 *
 *  Milestone 1 supports exactly one form: a reference to an inductive type
 *  declared in the same proof module.  Function types, type parameters, and
 *  primitives are deliberately absent — an unsupported source type must fail
 *  compilation rather than degrade into a catch-all node.
 */
enum ResolvedType extends Named:
  /** A reference to an inductive declared in the same module, with its type
   *  arguments in declaration order (empty for a non-generic enum). */
  case Inductive(id: SymbolId, name: String, args: List[ResolvedType] = Nil)
  /** A reference to a type parameter of the enclosing enum, definition, or
   *  theorem. */
  case TypeVar(id: SymbolId, name: String)

/** A binder: a method parameter, a pattern binder, or a local val. */
final case class ResolvedBinder(id: SymbolId, name: String, tpe: ResolvedType)

/** One constructor of an inductive type, with its fields in declaration order. */
final case class ResolvedConstructor(
  id:     SymbolId,
  name:   String,
  fields: List[ResolvedBinder],
  span:   SourceSpan,
)

/** An inductive type, with its constructors in declaration order. */
final case class ResolvedInductive(
  id:         SymbolId,
  name:       String,
  ctors:      List[ResolvedConstructor],
  span:       SourceSpan,
  /** Type parameters in declaration order; empty for a non-generic enum. */
  typeParams: List[ResolvedBinder] = Nil,
)

/** A verified expression. */
enum ResolvedExpr extends Spanned:
  /** A parameter, pattern binder, or local val in scope. */
  case Local(id: SymbolId, name: String, span: SourceSpan)

  /** A call to a verified definition — possibly the enclosing one (recursion).
   *  `typeArgs` are explicit: core passes type parameters as ordinary arguments,
   *  so what Scala inferred has to be written down. */
  case Call(target: SymbolId, name: String, args: List[ResolvedExpr],
            span: SourceSpan, typeArgs: List[ResolvedType] = Nil)

  /** A constructor application; `args.length` always equals the field count. */
  case Construct(inductive: SymbolId, ctor: SymbolId, ctorName: String,
                 args: List[ResolvedExpr], span: SourceSpan,
                 typeArgs: List[ResolvedType] = Nil)

  /** An exhaustive match with exactly one branch per constructor.
   *  `scrutineeType` is recorded because a branch's field types are stated in
   *  terms of the inductive's type parameters and must be instantiated at the
   *  scrutinee's actual type arguments. */
  case Match(scrutinee: ResolvedExpr, cases: List[ResolvedCase], span: SourceSpan,
             scrutineeType: ResolvedType)

  /** An immutable local binding. */
  case Let(binder: ResolvedBinder, value: ResolvedExpr, body: ResolvedExpr, span: SourceSpan)

/** One branch of a match: a constructor and its field binders, in field order. */
final case class ResolvedCase(
  ctor:     SymbolId,
  ctorName: String,
  binders:  List[ResolvedBinder],
  body:     ResolvedExpr,
  span:     SourceSpan,
)

/** A verified definition (an ordinary `def` inside a proof module). */
final case class ResolvedDef(
  id:     SymbolId,
  name:   String,
  params: List[ResolvedBinder],
  result: ResolvedType,
  body:   ResolvedExpr,
  span:   SourceSpan,
  /** Type parameters, which become leading `Type`-valued value parameters in
   *  core; empty for a non-generic definition. */
  typeParams: List[ResolvedBinder] = Nil,
)

/** An equality goal `lhs === rhs`, at a supported type. */
final case class ResolvedProp(
  tpe:  ResolvedType,
  lhs:  ResolvedExpr,
  rhs:  ResolvedExpr,
  span: SourceSpan,
)

/** A lemma handed to `simplify`. */
enum ResolvedLemmaRef extends Spanned:
  /** `ih(k)`, where `k` is the recursive field binder of the current branch. */
  case InductionHypothesis(binder: SymbolId, binderName: String, span: SourceSpan)

  /** A previously verified `@theorem` in the same module. */
  case Theorem(id: SymbolId, name: String, span: SourceSpan)

  /** A hypothesis bound by an enclosing `have`, named in the proof context. */
  case LocalHypothesis(name: String, span: SourceSpan)

/** A proof script.  Only the combinators actually implemented appear here. */
enum ResolvedTactic extends Spanned:
  case Trivial(span: SourceSpan)
  case Simplify(lemmas: List[ResolvedLemmaRef], span: SourceSpan)
  case Rewrite(equations: List[ResolvedLemmaRef], span: SourceSpan)
  case Induction(target: SymbolId, targetName: String,
                 cases: List[ResolvedTacticCase], span: SourceSpan)
  /** Induction whose hypothesis is quantified over `generalizing`, in the order
   *  written; each entry names another parameter of the same theorem. */
  case InductionGeneralizing(target: SymbolId, targetName: String,
                             generalizing: List[(SymbolId, String)],
                             cases: List[ResolvedTacticCase], span: SourceSpan)
  /** Constructor split with no induction hypothesis. */
  case Cases(target: SymbolId, targetName: String,
             cases: List[ResolvedTacticCase], span: SourceSpan)
  /** Close the goal with the induction hypothesis applied to `at`, in order.
   *
   *  The arguments are expressions, not just names: a generalized hypothesis is
   *  usually instantiated at a *changed* value (`Succ(acc)`, `derive(r, c)`),
   *  which is the whole reason the quantification was needed. */
  case ExactIh(at: List[ResolvedExpr], span: SourceSpan)
  /** Prove `lhs === rhs`, bind it as `name`, then run `continue` with it in scope.
   *  The claim's sides are expressions in the proof context, so they are
   *  translated there rather than in the theorem's parameter scope. */
  case Have(lhs: ResolvedExpr, rhs: ResolvedExpr, name: String,
            proof: ResolvedTactic, continue: ResolvedTactic, span: SourceSpan)

/** One branch of an `induction`, in the inductive's constructor order.
 *
 *  `usesIh` records whether the branch referenced `ih(...)`; the core proof
 *  context gains an induction hypothesis only when it does, which is what makes
 *  the existing `Builtins.induction` choose a `Fix`-wrapped proof term.
 */
final case class ResolvedTacticCase(
  ctor:     SymbolId,
  ctorName: String,
  binders:  List[ResolvedBinder],
  usesIh:   Boolean,
  tactic:   ResolvedTactic,
  span:     SourceSpan,
)

/** A `@theorem` method: parameters, an equality goal, and the script for it. */
final case class ResolvedTheorem(
  id:     SymbolId,
  name:   String,
  params: List[ResolvedBinder],
  goal:   ResolvedProp,
  tactic: ResolvedTactic,
  isSimp: Boolean,
  span:   SourceSpan,
  /** Type parameters, quantified ahead of the value parameters. */
  typeParams: List[ResolvedBinder] = Nil,
)

/** Everything extracted from one `@proofModule`. */
final case class ResolvedModule(
  id:          SymbolId,
  name:        String,
  inductives:  List[ResolvedInductive],
  definitions: List[ResolvedDef],
  theorems:    List[ResolvedTheorem],
  span:        SourceSpan,
)
