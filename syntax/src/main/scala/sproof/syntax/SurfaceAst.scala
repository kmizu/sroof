package sproof.syntax

/** Surface-level declarations (before elaboration). */
enum SDecl:
  case SInductive(name: String, params: List[SParam], ctors: List[SCtor])
  case SDef(name: String, params: List[SParam], retTpe: SType, body: SExpr)
  case SDefspec(name: String, params: List[SParam], prop: SType, proof: SProof)

/** Surface parameter (name: type). */
case class SParam(name: String, tpe: SType)

/** Surface constructor. */
case class SCtor(name: String, argParams: List[SParam], retTpe: SType)

/** Surface type expressions. */
enum SType:
  case STVar(name: String)
  case STApp(fn: SType, arg: SType)
  case STArrow(dom: SType, cod: SType)
  case STPi(name: String, dom: SType, cod: SType)
  case STUni(level: Int)
  case STEq(lhs: SExpr, rhs: SExpr)              // a = b (propositional equality)

/** Surface expressions. */
enum SExpr:
  case SEVar(name: String)
  case SEApp(fn: SExpr, args: List[SExpr])
  case SELam(params: List[SParam], body: SExpr)
  case SEMatch(scrutinee: SExpr, cases: List[SMatchCase])
  case SECon(typeName: String, ctorName: String, args: List[SExpr])

/** Match case in surface syntax. */
case class SMatchCase(ctor: String, bindings: List[String], body: SExpr)

/** Proof terms / tactics. */
enum SProof:
  case SBy(tactic: STactic)
  case STerm(expr: SExpr)

/** Surface tactics. */
enum STactic:
  case STrivial
  case STriv
  case SAssume(names: List[String])
  case SApply(expr: SExpr)
  case SSimplify(lemmas: List[String])
  case SSimp(lemmas: List[String])
  case SInduction(varName: String, cases: List[STacticCase])
  case SSorry

/** A case in an induction tactic. */
case class STacticCase(ctorName: String, extraBindings: List[String], tactic: STactic)
