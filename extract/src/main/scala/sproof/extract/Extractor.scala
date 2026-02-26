package sproof.extract

import sproof.core.{Term, GlobalEnv, IndDef, CtorDef}

/** Extracts sproof core terms to Scala 3 source code.
 *
 *  The extractor erases proof-irrelevant information (type universes, propositions)
 *  and generates idiomatic Scala 3 code from the dependently-typed term representation.
 *
 *  Key design decisions:
 *  - `Term.Uni` is erased to `Any` (type universes have no runtime meaning)
 *  - `defspec` (theorem statements) are erased to `Unit` / `()`
 *  - De Bruijn indices are resolved using a `ctx` name list
 *  - Inductive types become Scala 3 `enum` declarations
 *  - `Term.Fix` becomes a `def` with recursion (named by the Fix binder)
 */
/** Names of inductive types that are mapped to Scala built-in types.
 *
 *  These types are NOT emitted as `enum` declarations; instead the
 *  Scala primitive is used directly.  Constructor expressions and
 *  pattern matches are translated to arithmetic.
 *
 *  | sproof        | Scala             |
 *  |---------------|-------------------|
 *  | Int           | Int               |
 *  | Int.zero      | 0                 |
 *  | Int.pos(n)    | n + 1             |
 *  | Int.neg(n)    | -(n + 1)          |
 *  | match (Int)   | if / else if / else |
 */
val builtinInductives: Set[String] = Set("Int")

object Extractor:

  // ---- public API ----

  /** Extract a full sproof program to Scala 3 source. */
  def extractProgram(env: GlobalEnv): String =
    val indParts = env.inductives.values.toList
      .sortBy(_.name)
      .map(extractInductive)
    val defParts = env.defs.values.toList
      .sortBy(_.name)
      .map(d => extractDef(d.name, d.tpe, d.body))
    (indParts ++ defParts).mkString("\n\n")

  /** Extract an inductive type definition to a Scala 3 `enum`.
   *
   *  Builtin inductive types (e.g. `Int`) are NOT emitted as enums;
   *  a comment is produced instead and Scala's built-in type is used.
   *
   *  Example:
   *  {{{
   *    IndDef("Nat", [], [CtorDef("zero",[]), CtorDef("succ",[Nat])], 0)
   *    // produces:
   *    enum Nat:
   *      case Zero
   *      case Succ(n: Nat)
   *  }}}
   */
  def extractInductive(indDef: IndDef): String =
    val name = indDef.name
    if builtinInductives.contains(name) then
      s"// $name is mapped to Scala's built-in $name"
    else
      val ctors  = indDef.ctors.map(c => extractCtor(name, c))
      val header = s"enum $name:"
      if ctors.isEmpty then s"$header\n  case Empty"
      else ctors.map(c => s"  $c").mkString(s"$header\n", "\n", "")

  /** Extract a function definition.
   *
   *  Peels off leading `Lam` binders to collect parameters, then renders the body.
   *  Example: `def add(n: Nat)(m: Nat): Nat = n match { ... }`
   */
  def extractDef(name: String, tpe: Term, body: Term): String =
    val (params, retTpe, bodyTerm) = peelLambdas(body, tpe, Nil)
    val paramStr = params.map((n, t) => s"($n: $t)").mkString("")
    val retStr   = termToScalaType(retTpe)
    val ctx      = params.map(_._1)
    val bodyStr  = termToScalaExpr(bodyTerm, ctx)
    s"def $name$paramStr: $retStr = $bodyStr"

  /** Extract a theorem (defspec) — erased to `Unit` at runtime.
   *
   *  Theorem statements carry no computational content, so we erase them.
   */
  def extractDefspec(name: String, params: List[(String, Term)]): String =
    val paramStr = params.map((n, t) => s"($n: ${termToScalaType(t)})").mkString("")
    s"def $name$paramStr: Unit = ()"

  /** Convert a Term to a Scala 3 type expression. */
  def termToScalaType(t: Term): String = t match
    case Term.Uni(_)             => "Any"
    case Term.Ind(name, _, _)    => name
    case Term.Var(i)             => s"T$i"        // free type variable (fallback)
    case Term.Pi(x, dom, cod)    =>
      if Term.freeIn(0, cod) then
        // Dependent Pi: rendered as generic function type (simplified)
        s"[${sanitizeName(x)} <: ${termToScalaType(dom)}] =>> ${termToScalaType(cod)}"
      else
        s"${termToScalaType(dom)} => ${termToScalaType(cod)}"
    case Term.App(f, a)          => s"${termToScalaType(f)}[${termToScalaType(a)}]"
    case Term.Lam(x, _, b)      => termToScalaType(b)   // type-level lambda (erased)
    case Term.Let(_, _, _, b)   => termToScalaType(b)
    case Term.Con(_, ind, _)    => ind
    case Term.Fix(name, _, _)   => name
    case Term.Meta(_)            => "Any"
    case Term.Mat(_, _, rt)     => termToScalaType(rt)

  /** Convert a Term to a Scala 3 expression.
   *
   *  @param t   the core term to extract
   *  @param ctx name list for De Bruijn resolution; head = index 0 (most recent binder)
   */
  def termToScalaExpr(t: Term, ctx: List[String] = Nil): String = t match
    case Term.Var(i) =>
      ctx.lift(i).getOrElse(s"_v$i")

    case Term.App(f, a) =>
      val fStr = termToScalaExpr(f, ctx)
      val aStr = termToScalaExpr(a, ctx)
      // Detect constructor-style application for nicer output
      s"$fStr($aStr)"

    case Term.Lam(x, _, b) =>
      val safe = sanitizeName(x)
      val bStr = termToScalaExpr(b, safe :: ctx)
      s"($safe => $bStr)"

    case Term.Let(x, _, d, b) =>
      val safe = sanitizeName(x)
      val dStr = termToScalaExpr(d, ctx)
      val bStr = termToScalaExpr(b, safe :: ctx)
      s"{ val $safe = $dStr; $bStr }"

    case Term.Pi(x, _, _) =>
      // Pi terms in expression position are types — erase to Any
      "Any"

    case Term.Uni(_) => "()"  // universe in expression position → unit

    case Term.Ind(name, _, _) => name   // reference to inductive type constructor

    case Term.Con(name, indRef, args) =>
      // Builtin constructors are translated to arithmetic literals.
      if builtinInductives.contains(indRef) then
        extractBuiltinCon(name, indRef, args, ctx)
      else
        val ctorName = pascalCase(name)
        val fullName = s"$indRef.$ctorName"
        if args.isEmpty then fullName
        else
          val argStrs = args.map(termToScalaExpr(_, ctx))
          s"$fullName(${argStrs.mkString(", ")})"

    case Term.Mat(scrutinee, cases, retTpe) =>
      // Check if the scrutinee's type is a builtin inductive.
      val indName = retTpe match
        case Term.Ind(n, _, _) if builtinInductives.contains(n) => Some(n)
        case _ =>
          // Infer from the first case's ctor owning type when retTpe is opaque.
          cases.headOption.flatMap(mc => builtinInductives.find(_ => true).filter(_ =>
            // crude: if ANY case ctor is from a builtin, treat as builtin match
            cases.forall(c => List("zero","pos","neg").contains(c.ctor))
          ))
      indName match
        case Some(ind) => extractBuiltinMatch(scrutinee, cases, ind, ctx)
        case None      => extractMatch(scrutinee, cases, ctx)

    case Term.Fix(name, _, body) =>
      // Fix point: render as a local recursive def
      val safe = sanitizeName(name)
      val bodyStr = termToScalaExpr(body, safe :: ctx)
      s"{ def $safe: Any = $bodyStr; $safe }"

    case Term.Meta(id) => s"???"  // unsolved metavariable

  // ---- private helpers ----

  /** Translate a builtin constructor to a Scala arithmetic expression.
   *
   *  | Constructor      | Scala output  |
   *  |-----------------|---------------|
   *  | Int.zero        | 0             |
   *  | Int.pos(n)      | n + 1         |
   *  | Int.neg(n)      | -(n + 1)      |
   */
  private def extractBuiltinCon(
    name:   String,
    indRef: String,
    args:   List[Term],
    ctx:    List[String],
  ): String = (indRef, name) match
    case ("Int", "zero")          => "0"
    case ("Int", "pos") if args.size == 1 =>
      val n = termToScalaExpr(args.head, ctx)
      s"$n + 1"
    case ("Int", "neg") if args.size == 1 =>
      val n = termToScalaExpr(args.head, ctx)
      s"-($n + 1)"
    case _ =>
      // Fallback: emit as normal constructor
      val ctorName = pascalCase(name)
      val fullName = s"$indRef.$ctorName"
      if args.isEmpty then fullName
      else s"$fullName(${args.map(termToScalaExpr(_, ctx)).mkString(", ")})"

  /** Translate a match on a builtin Int to an if/else chain.
   *
   *  Expects exactly three cases in order: zero, pos(n), neg(n).
   *  Emits:
   *  {{{
   *    if (scrut == 0) body0
   *    else if (scrut > 0) { val n = scrut - 1; bodyP }
   *    else { val n = -scrut - 1; bodyN }
   *  }}}
   */
  private def extractBuiltinMatch(
    scrutinee: Term,
    cases:     List[sproof.core.MatchCase],
    ind:       String,
    ctx:       List[String],
  ): String =
    val sStr = termToScalaExpr(scrutinee, ctx)
    // Partition cases by ctor name (order-insensitive)
    val byName = cases.map(mc => mc.ctor -> mc).toMap
    def arm(mc: sproof.core.MatchCase, binder: String => String): String =
      if mc.bindings == 0 then termToScalaExpr(mc.body, ctx)
      else
        val bindName  = s"_n"
        val extCtx    = bindName :: ctx
        val bodyStr   = termToScalaExpr(mc.body, extCtx)
        s"{ val $bindName = ${binder(sStr)}; $bodyStr }"

    (byName.get("zero"), byName.get("pos"), byName.get("neg")) match
      case (Some(z), Some(p), Some(n)) =>
        val zBody = termToScalaExpr(z.body, ctx)
        val pBody = arm(p, s => s"$s - 1")
        val nBody = arm(n, s => s"-$s - 1")
        s"(if ($sStr == 0) $zBody else if ($sStr > 0) $pBody else $nBody)"
      case _ =>
        // Fallback to normal match if case structure is unexpected
        extractMatch(scrutinee, cases, ctx)

  /** Render a match expression. */
  private def extractMatch(
    scrutinee: Term,
    cases:     List[sproof.core.MatchCase],
    ctx:       List[String],
  ): String =
    val sStr = termToScalaExpr(scrutinee, ctx)
    if cases.isEmpty then s"($sStr match {})"
    else
      val caseStrs = cases.map { mc =>
        val bindNames = (0 until mc.bindings).toList.map(i => s"_arg${mc.bindings - 1 - i}")
        // In the case body, new binders are at the head of ctx (innermost = Var(0))
        val extCtx    = bindNames.reverse ++ ctx
        val bodyStr   = termToScalaExpr(mc.body, extCtx)
        val ctorName  = pascalCase(mc.ctor)
        if bindNames.isEmpty then
          s"    case _.$ctorName => $bodyStr"
        else
          s"    case _.$ctorName(${bindNames.mkString(", ")}) => $bodyStr"
      }
      s"($sStr match {\n${caseStrs.mkString("\n")}\n  })"

  /** Extract a constructor's Scala `case` line for an enum.
   *
   *  Constructor argument names are generated as `arg0`, `arg1`, etc.
   *  Argument types are resolved relative to the enclosing inductive type name.
   */
  private def extractCtor(indName: String, ctor: CtorDef): String =
    val ctorName = pascalCase(ctor.name)
    if ctor.argTpes.isEmpty then s"case $ctorName"
    else
      val args = ctor.argTpes.zipWithIndex.map { (tpe, i) =>
        val argName = s"arg$i"
        val tpeStr  = termToScalaType(tpe) match
          case "T0" => indName   // self-reference: free Var(0) in recursive ctors
          case t    => t
        s"$argName: $tpeStr"
      }
      s"case $ctorName(${args.mkString(", ")})"

  /** Peel leading `Lam` binders off `body` collecting (paramName, scalaType) pairs.
   *
   *  Simultaneously peels corresponding `Pi` binders off `tpe` to get the return type.
   *  Returns (params, returnType, innerBody).
   */
  private def peelLambdas(
    body:   Term,
    tpe:    Term,
    params: List[(String, String)],
  ): (List[(String, String)], Term, Term) = (body, tpe) match
    case (Term.Lam(x, paramTpe, b), Term.Pi(_, _, cod)) =>
      val safe     = sanitizeName(x)
      val tpeStr   = termToScalaType(paramTpe)
      peelLambdas(b, cod, params :+ (safe, tpeStr))
    case (Term.Lam(x, paramTpe, b), _) =>
      val safe   = sanitizeName(x)
      val tpeStr = termToScalaType(paramTpe)
      peelLambdas(b, tpe, params :+ (safe, tpeStr))
    case _ =>
      (params, tpe, body)

  /** Convert a sproof name to PascalCase for enum case names.
   *
   *  "zero" → "Zero", "succ" → "Succ", already-Pascal strings unchanged.
   */
  private def pascalCase(s: String): String =
    if s.isEmpty then s
    else s.head.toUpper.toString + s.tail

  /** Sanitize a binder name to a valid Scala identifier. */
  private def sanitizeName(s: String): String =
    if s.isEmpty || s == "_" then "_"
    else s.filter(c => c.isLetterOrDigit || c == '_')
      .ensuring(_.nonEmpty, "_")
