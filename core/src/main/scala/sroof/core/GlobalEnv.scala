package sroof.core

/** Definition of a constructor in a global inductive type.
 *
 *  `argTpes` lists argument types left-to-right.
 *  In a match body with `bindings = argTpes.length`, the last arg = Var(0),
 *  second-to-last = Var(1), etc. (standard De Bruijn convention).
 *
 *  `retIndices`: the concrete index values in the constructor's return type.
 *  For example, Vec.vnil has retIndices = [Nat.zero], Vec.vcons has [Nat.succ(m)].
 *  Empty for non-indexed types like Nat.
 *
 *  Written by `Elaborator.elabInductive` (since v0.8) and read by
 *  `IndChecker.ctorIndexValues` (since v0.10) to derive a constructor's type
 *  instead of echoing back the expected one.  It uses the same progressive
 *  De Bruijn convention as the *last* entry of `argTpes`, so it may mention the
 *  constructor's own arguments: Var(0..n-1) are those arguments in reverse,
 *  then the type's indices, then its parameters.
 *
 *  Empty is not "index zero" but "this constructor states no index" — the shape
 *  of every declaration written before indexed return types were expressible.
 *  `IndChecker` treats such a family as un-indexed, which is what keeps
 *  `stdlib/Vec.sroof` meaning what it always meant.
 */
case class CtorDef(
  name:       String,
  argTpes:    List[Term],
  retIndices: List[Term] = Nil,
)

/** Definition of an inductive type in the global environment.
 *
 *  `universe`: the type universe level.  `Ind(name) : Type_universe`.
 *  `params`:   uniform type parameters (e.g. A: Type in List(A)).
 *              Params with Uni type become Scala type parameters during extraction.
 *  `ctors`:    constructor definitions, ordered as declared.
 *  `indices`:  index parameters that vary per constructor (e.g. n: Nat in Vec(A)(n)).
 *              Indices are fully erased during Scala 3 extraction.
 */
case class IndDef(
  name:     String,
  params:   List[Param],
  ctors:    List[CtorDef],
  universe: Int,
  indices:  List[Param] = Nil,
)

/** A global function definition. */
case class DefEntry(
  name: String,
  tpe:  Term,
  body: Term,
)

/** A structure (record/type-class interface) definition.
 *
 *  Desugars to an inductive type with a single `mk` constructor + field accessors.
 *  Kept separately so the elaborator can validate instance bindings.
 */
case class StructDef(
  name:   String,
  fields: List[(String, Term)],  // (fieldName, fieldType) in declaration order
)

/** Global environment of inductive type definitions and function definitions.
 *
 *  Passed as a contextual parameter (`using`) to the bidirectional type checker
 *  so that `Con` and `Mat` nodes can be checked against known inductive types.
 *
 *  The `given GlobalEnv = GlobalEnv.empty` in the companion object provides a
 *  backward-compatible default, so existing call-sites without explicit inductives
 *  compile unchanged.
 */
case class GlobalEnv(
  inductives: Map[String, IndDef],
  defs:       Map[String, DefEntry],
  structures: Map[String, StructDef] = Map.empty,
  /** Maps operator symbol (e.g. "+") to the def name that implements it.
   *  No overloading: each symbol has exactly one registered implementation. */
  operators:  Map[String, String]    = Map.empty,
  /** Set of def names marked @[simp] — used by the simplify tactic as default lemmas. */
  simpSet:    Set[String]            = Set.empty,
):
  def lookupInd(name: String):     Option[IndDef]    = inductives.get(name)
  def lookupDef(name: String):     Option[DefEntry]  = defs.get(name)
  def lookupStruct(name: String):  Option[StructDef] = structures.get(name)
  def lookupOperator(op: String):  Option[String]    = operators.get(op)

  def addInd(d: IndDef):                    GlobalEnv = copy(inductives = inductives + (d.name -> d))
  def addDef(d: DefEntry):                  GlobalEnv = copy(defs       = defs       + (d.name -> d))
  def addStruct(s: StructDef):              GlobalEnv = copy(structures = structures + (s.name -> s))
  def addOperator(sym: String, fn: String): GlobalEnv = copy(operators = operators + (sym -> fn))
  def addToSimpSet(name: String):           GlobalEnv = copy(simpSet   = simpSet + name)

object GlobalEnv:
  val empty: GlobalEnv = GlobalEnv(Map.empty, Map.empty, Map.empty, Map.empty, Set.empty)

  /** Default implicit: empty environment.
   *  Lower priority than locally-defined givens; existing code needing no inductives
   *  compiles without importing anything.
   */
  given GlobalEnv = empty

  // ---- Built-in: Nat ----

  private val natInd: Term = Term.Ind("Nat", Nil, Nil)

  val natDef: IndDef = IndDef(
    name     = "Nat",
    params   = Nil,
    ctors    = List(
      CtorDef("zero", Nil),
      CtorDef("succ", List(natInd)),
    ),
    universe = 0,
  )

  /** Global environment containing only the Nat inductive type. */
  val withNat: GlobalEnv = empty.addInd(natDef)
