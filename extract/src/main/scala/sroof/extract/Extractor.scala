package sroof.extract

import sroof.core.{Term, GlobalEnv, IndDef, CtorDef, Param}

/** Extracts sroof core terms to Scala 3 source code.
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
 *  | sroof        | Scala             |
 *  |---------------|-------------------|
 *  | Int           | Int               |
 *  | Int.zero      | 0                 |
 *  | Int.pos(n)    | n + 1             |
 *  | Int.neg(n)    | -(n + 1)          |
 *  | match (Int)   | if / else if / else |
 */
val builtinInductives: Set[String] = Set("Int")

/** A binder visible to the renderer.
 *
 *  One list serves both the expression and the type renderer, because a De Bruijn
 *  index means the same slot in either. `isType` records whether that slot holds a
 *  `Type`-valued parameter — the only kind whose name is usable as a Scala *type*.
 *  A value binder mentioned in a type is a dependency Scala cannot express, and is
 *  erased to `Any` rather than emitted as a name that does not resolve.
 */
final case class Binder(
  name:   String,
  isType: Boolean,
  isSelf: Boolean         = false,
  /** The inductive this slot's value belongs to, when its type says so. A `match`
   *  case names its constructor but not its type, and two records may both call
   *  their constructor `mk`; the scrutinee's binder is what tells them apart. */
  ind:    Option[String]  = None,
)

/** Context the renderer needs that a term does not carry.
 *
 *  The core has no node for "reference to a global definition": the elaborator
 *  inlines a def's body at every use site. Extraction has to *re-find* those
 *  copies — otherwise a program with n uses of `plus` emits n copies of `plus`,
 *  and each copy appears in expression position as `{ def plus = …; plus }(x)(y)`,
 *  which does not even parse.
 */
final case class ExtractCtx(
  /** A recursive def's stored body → the Scala name to emit instead of inlining. */
  defNames:     Map[Term, String]                = Map.empty,
  /** Def name → argument positions hoisted into a Scala type-parameter list. */
  typeArgs:     Map[String, Set[Int]]            = Map.empty,
  /** Inductive name → how many Scala type parameters its `enum` declares. */
  indArity:     Map[String, Int]                 = Map.empty,
  /** (inductive, constructor) → argument positions that survive erasure. */
  ctorDataArgs: Map[(String, String), List[Int]] = Map.empty,
  /** Constructor name → the same positions, when the name is unambiguous. */
  ctorArgsByName: Map[String, List[Int]]         = Map.empty,
  /** Constructor name → the inductive that declares it, when only one does. */
  ctorOwner:      Map[String, String]            = Map.empty,
  /** Every inductive the program declares. Anything else in type position is a
   *  proposition (`Eq`, and the built-ins the kernel knows) and is erased. */
  knownInds:    Set[String]                      = Set.empty,
  /** Built-ins this program may actually be translated to arithmetic. */
  arithmetic:   Set[String]                      = builtinInductives,
)

object ExtractCtx:
  val empty: ExtractCtx = ExtractCtx()

/** One parameter of an extracted `def`, before it is split into `[A]` and `(x: T)`. */
private final case class DefParam(name: String, tpe: Term, isType: Boolean)

object Extractor:

  // ---- public API ----

  /** Extract a full sroof program to Scala 3 source. */
  def extractProgram(env: GlobalEnv): String =
    val ectx = buildCtx(env)
    val indParts = env.inductives.values.toList
      .sortBy(_.name)
      .map(i => extractInductive(i, ectx))
    val defParts = env.defs.values.toList
      .sortBy(_.name)
      .map(d => extractDef(d.name, d.tpe, d.body, ectx))
    val runtimeParts =
      if hasDefaultIoShape(env) then List(extractIoRuntime)
      else Nil
    (indParts ++ defParts ++ runtimeParts).mkString("\n\n")

  /** Collect everything the renderer cannot read off a single term. */
  def buildCtx(env: GlobalEnv): ExtractCtx =
    // Only `Fix`-shaped bodies are recognised by structure. A non-recursive def's
    // body can be as small as `Con("zero")`, and keying on that would rename every
    // `zero` in the program after the def that happens to alias it.
    val defNames = env.defs.values.collect {
      case d if d.body.isInstanceOf[Term.Fix] => d.body -> sanitizeName(d.name)
    }.toMap
    val typeArgs = env.defs.values
      .map(d => sanitizeName(d.name) -> typeParamPositions(d.tpe))
      .toMap
    val indArity = env.inductives.values
      .map(i => i.name -> i.params.count(p => isTypeParam(p.tpe)))
      .toMap
    val known = env.inductives.keySet.toSet ++ builtinInductives
    val ctorDataArgs = (
      for
        ind  <- env.inductives.values
        ctor <- ind.ctors
      yield (ind.name, ctor.name) -> dataArgPositions(ind, ctor, known)
    ).toMap
    // A `match` case names its constructor but not the inductive it belongs to, so
    // the same erasure has to be reachable by constructor name. A name two
    // inductives disagree about is left out rather than guessed.
    val byName = ctorDataArgs.toList
      .groupBy(_._1._2)
      .collect { case (n, entries) if entries.map(_._2).distinct.sizeIs == 1 => n -> entries.head._2 }
    // Two enums may both declare a `mk`, and both wildcard imports are in scope by
    // the time either is used — `Reference to Mk is ambiguous`.  Knowing the owner
    // lets a pattern name it.
    val owners = ctorDataArgs.keys.toList
      .groupBy(_._2)
      .collect { case (c, ks) if ks.map(_._1).distinct.sizeIs == 1 => c -> ks.head._1 }
    // `Int.pos(n)` becomes `n + 1` only if `n` is itself an `Int`. `examples/int.sroof`
    // declares `pos(n: Nat)`, so the arithmetic reading bound `_n` as an `Int` and
    // handed it to a branch expecting a `Nat`. When the declaration does not have the
    // shape the mapping assumes, the mapping does not apply and the inductive is
    // extracted as itself. A built-in the program never declares keeps the mapping —
    // there is nothing else it could mean.
    val arithmetic = builtinInductives.filter { n =>
      val shapeFits =
        env.inductives.get(n).forall(_.ctors.forall(_.argTpes.forall(headInductive(_).contains(n))))
      shapeFits || !usedAsData(env, n)
    }
    ExtractCtx(defNames, typeArgs, indArity, ctorDataArgs, byName, owners, known, arithmetic)

  private def isTypeParam(t: Term): Boolean = t match
    case Term.Uni(_) => true
    case _           => false

  /** Does the program build or take apart values of this inductive?
   *
   *  `stdlib/Effect.sroof` declares an `Int` that does not fit the arithmetic shape
   *  but never constructs or matches one — for it, `Int` is Scala's `Int` and the IO
   *  runtime depends on that. `examples/int.sroof` declares the same type and works
   *  with it, and there the mapping turned `pos(n: Nat)` into `n + 1` and bound the
   *  match variable as an `Int` for a branch expecting a `Nat`. Only the second is a
   *  conflict, and only the second gives up the mapping.
   */
  private def usedAsData(env: GlobalEnv, name: String): Boolean =
    val ctorNames = env.inductives.get(name).map(_.ctors.map(_.name).toSet).getOrElse(Set.empty)
    def go(t: Term): Boolean = t match
      case Term.Con(_, ind, args) if ind == name && args.nonEmpty => true
      case Term.Con(_, _, args)   => args.exists(go)
      case Term.Mat(scrut, cs, rt) =>
        (cs.nonEmpty && ctorNames.nonEmpty && cs.forall(c => ctorNames.contains(c.ctor))) ||
        go(scrut) || go(rt) || cs.exists(c => go(c.body))
      case Term.App(f, a)        => go(f) || go(a)
      case Term.Lam(_, tp, b)    => go(tp) || go(b)
      case Term.Pi(_, d, c)      => go(d) || go(c)
      case Term.Let(_, tp, d, b) => go(tp) || go(d) || go(b)
      case Term.Fix(_, tp, b)    => go(tp) || go(b)
      case _                     => false
    env.defs.values.exists(d => go(d.body))

  /** The inductive a type is headed by, if any. */
  private def headInductive(t: Term): Option[String] = spine(t, Nil)._1 match
    case Term.Ind(n, _, _) => Some(n)
    case _                 => None

  /** Positions of `Type`-valued parameters, which extraction hoists into `[A, …]`.
   *
   *  `.sroof` has no separate type-parameter list: `def poly_length(A: Type, xs:
   *  PolyList(A))` passes the element type as an ordinary argument. Left as a value
   *  parameter it has no Scala type to be given, and every mention of `A` in the
   *  signature refers to a *value*.
   */
  private def typeParamPositions(tpe: Term): Set[Int] =
    def go(t: Term, i: Int, acc: Set[Int]): Set[Int] = t match
      case Term.Pi(_, dom, cod) => go(cod, i + 1, if isTypeParam(dom) then acc + i else acc)
      case _                    => acc
    go(tpe, 0, Set.empty)

  /** Constructor argument positions that survive erasure.
   *
   *  Only *proofs* go. An index argument looks erasable — the `enum` header drops
   *  the index parameter — but the argument itself is ordinary runtime data: a
   *  function that takes the length of a vector as a parameter is passed the field
   *  a `Cons` stored, and dropping it leaves that call with nothing to pass.
   *
   *  Whatever is dropped here has to be dropped identically by `Term.Con` and by
   *  every `match` pattern, or the declaration takes two arguments while the use
   *  sites pass three.
   */
  private def dataArgPositions(ind: IndDef, ctor: CtorDef, known: Set[String]): List[Int] =
    ctor.argTpes.zipWithIndex.collect { case (t, i) if !isProofType(t, known) => i }

  /** Is this the type of a proof rather than of data?
   *
   *  A type headed by an inductive the program never declared is one the kernel
   *  supplies — `Eq` above all — and carries no runtime content. Emitting it
   *  produced `arg1: Eq[isValidCodepoint, Bool]`, naming three types that do not
   *  exist in the extracted program.
   */
  private def isProofType(t: Term, known: Set[String]): Boolean =
    known.nonEmpty && (spine(t, Nil)._1 match
      case Term.Ind(n, _, _) => !known.contains(n)
      case _                 => false)

  /** Does the term mention a function type anywhere? */
  private def containsPi(t: Term): Boolean = t match
    case Term.Pi(_, _, _)     => true
    case Term.App(f, a)       => containsPi(f) || containsPi(a)
    case Term.Lam(_, tp, b)   => containsPi(tp) || containsPi(b)
    case Term.Let(_, tp, d, b) => containsPi(tp) || containsPi(d) || containsPi(b)
    case Term.Con(_, _, as)   => as.exists(containsPi)
    case Term.Mat(s, cs, rt)  => containsPi(s) || containsPi(rt) || cs.exists(c => containsPi(c.body))
    case Term.Fix(_, tp, b)   => containsPi(tp) || containsPi(b)
    case _                    => false

  /** Extract an inductive type definition to a Scala 3 `enum`.
   *
   *  Builtin inductive types (e.g. `Int`) are NOT emitted as enums;
   *  a comment is produced instead and Scala's built-in type is used.
   *
   *  Uniform parameters with `Uni` type become Scala type parameters (e.g. `[A]`).
   *  Index parameters (`IndDef.indices`) are fully erased — they appear neither in the
   *  enum header nor in constructor argument lists.
   *
   *  Example:
   *  {{{
   *    IndDef("Nat", [], [CtorDef("zero",[]), CtorDef("succ",[Nat])], 0)
   *    // produces:
   *    enum Nat:
   *      case Zero
   *      case Succ(n: Nat)
   *
   *    IndDef("Vec", [A:Uni], [nil,cons(Nat,A,Vec[A])], 0, indices=[n:Nat])
   *    // produces:
   *    enum Vec[A]:
   *      case Nil
   *      case Cons(arg0: A, arg1: Vec[A])
   *  }}}
   */
  def extractInductive(indDef: IndDef, ectx: ExtractCtx = ExtractCtx.empty): String =
    val name = indDef.name
    if ectx.arithmetic.contains(name) then
      s"// $name is mapped to Scala's built-in $name"
    else
      // Params with Uni type become Scala type parameters [A, B, ...]
      val typeParams = indDef.params.collect { case Param(n, Term.Uni(_)) => n }
      // A parameterless case in an invariant generic enum has no way to fix its
      // type argument — dotc reports `cannot determine type argument for enum
      // parent class`.  Covariance is what makes `case Nil` mean `Vec[Nothing]`
      // and therefore usable wherever a `Vec[A]` is wanted.  It is only claimed
      // when no constructor field is a function type, since a parameter to the
      // left of an arrow would be a genuine contravariant occurrence.
      val variance =
        if indDef.ctors.forall(_.argTpes.forall(t => !containsPi(t))) then "+" else ""
      val typeParamStr =
        if typeParams.isEmpty then "" else s"[${typeParams.map(variance + _).mkString(", ")}]"
      val header = s"enum $name$typeParamStr:"
      val ctors  = indDef.ctors.map(c => extractCtor(indDef, c, typeParams, ectx))
      // The wildcard import is what makes an unqualified `case Zero =>` pattern
      // resolve in the definitions below.
      val importLine = s"\nimport $name.*"
      if ctors.isEmpty then s"$header\n  case Empty$importLine"
      else ctors.map(c => s"  $c").mkString(s"$header\n", "\n", importLine)

  /** Extract a function definition.
   *
   *  Peels off leading `Lam` binders to collect parameters, then renders the body.
   *  Example: `def add(n: Nat)(m: Nat): Nat = n match { ... }`
   */
  def extractDef(name: String, tpe: Term, body: Term, ectx: ExtractCtx = ExtractCtx.empty): String =
    val safe = sanitizeName(name)
    // A recursive def is stored as `Fix(self, τ, λ…)`. Peeling stops at the `Fix`,
    // so without this the whole def stays a *value* whose type is the dependent
    // function type — rendered as a type lambda, `def concat: [A <: Any] =>> …`,
    // which is not a term type. Unwrapping puts the parameters in the signature;
    // the Fix binder keeps slot 0 and now names the def itself.
    val (inner, selfSlot) = body match
      case Term.Fix(_, _, b) => (b, List(Binder(safe, false, isSelf = true)))
      case b                 => (b, Nil)
    val (params, retTpe, bodyTerm) = peelLambdas(inner, tpe, Nil)
    val binders = params.map(p => Binder(p.name, p.isType, ind = headInductive(p.tpe)))
    // Each parameter's type sees only the parameters before it, innermost first.
    def scopeUpTo(k: Int): List[Binder] = binders.take(k).reverse
    val valueParamStr = params.zipWithIndex
      .filterNot(_._1.isType)
      .map((p, k) => s"(${p.name}: ${typeStr(p.tpe, scopeUpTo(k), ectx)})")
      .mkString
    val typeParams  = params.filter(_.isType).map(_.name)
    val typeParamStr = if typeParams.isEmpty then "" else s"[${typeParams.mkString(", ")}]"
    val retStr  = typeStr(retTpe, scopeUpTo(params.length), ectx)
    val bodyStr = exprStr(bodyTerm, binders.reverse ++ selfSlot, ectx)
    s"def $safe$typeParamStr$valueParamStr: $retStr = $bodyStr"

  /** Extract a theorem (defspec) — erased to `Unit` at runtime.
   *
   *  Theorem statements carry no computational content, so we erase them.
   */
  def extractDefspec(name: String, params: List[(String, Term)]): String =
    val paramStr = params.map((n, t) => s"($n: ${termToScalaType(t)})").mkString("")
    s"def $name$paramStr: Unit = ()"

  /** Convert a Term to a Scala 3 type expression.
   *
   *  @param t          the type term to convert
   *  @param paramNames names of enclosing inductive type parameters, innermost first.
   *                    Used to resolve `Var(i)` references inside constructor arg types.
   *                    E.g. for Vec[A], paramNames=["A"], so Var(0) → "A".
   */
  def termToScalaType(t: Term, paramNames: List[String] = Nil): String =
    typeStr(t, paramNames.map(Binder(_, true)), ExtractCtx.empty)

  /** The type renderer proper.
   *
   *  Two rules earn their keep:
   *
   *  - An unresolved `Var` becomes `Any`, never `T0`. A name that is not declared
   *    anywhere fails with `Not found: type T0`; `Any` is at worst too weak.
   *  - An applied inductive keeps only as many arguments as its `enum` declares
   *    type parameters. Indices are erased from the declaration, so carrying them
   *    into the use site produced `Vec[A][n]` — an over-application of a type that
   *    takes one parameter.
   */
  private def typeStr(t: Term, scope: List[Binder], e: ExtractCtx): String = t match
    case Term.Uni(_)          => "Any"
    case Term.Ind(name, _, _) =>
      if e.knownInds.nonEmpty && !e.knownInds.contains(name) then "Unit" else name
    case Term.Var(i)          => scope.lift(i).filter(_.isType).map(_.name).getOrElse("Any")

    case Term.Pi(x, dom, cod) =>
      // A `Type`-valued domain is a type parameter; extraction hoists those into a
      // separate list, so at this position it contributes nothing.
      if isTypeParam(dom) then typeStr(cod, Binder(sanitizeName(x), true) :: scope, e)
      else s"${typeStr(dom, scope, e)} => ${typeStr(cod, Binder(sanitizeName(x), false) :: scope, e)}"

    case Term.App(_, _) =>
      val (head, args) = spine(t, Nil)
      head match
        case Term.Ind(name, _, _) =>
          val keep = args.take(e.indArity.getOrElse(name, args.length))
          if keep.isEmpty then name
          else s"$name[${keep.map(a => typeStr(a, scope, e)).mkString(", ")}]"
        case _ =>
          // Applying anything else is a dependency (`B(a)`, `plus(n, m)`) that has
          // no Scala type-level reading. Keep the head; drop what it is applied to.
          typeStr(head, scope, e)

    case Term.Lam(x, tp, b)   => typeStr(b, Binder(sanitizeName(x), isTypeParam(tp)) :: scope, e)
    case Term.Let(x, _, _, b) => typeStr(b, Binder(sanitizeName(x), false) :: scope, e)
    case Term.Con(_, ind, _)  => ind
    case Term.Fix(name, _, _) => sanitizeName(name)
    case Term.Meta(_)         => "Any"
    case Term.Mat(_, _, rt)   => typeStr(rt, scope, e)

  /** Flatten an application into its head and arguments, outermost-last. */
  private def spine(t: Term, acc: List[Term]): (Term, List[Term]) = t match
    case Term.App(f, a) => spine(f, a :: acc)
    case _              => (t, acc)

  /** Convert a Term to a Scala 3 expression.
   *
   *  @param t   the core term to extract
   *  @param ctx name list for De Bruijn resolution; head = index 0 (most recent binder)
   */
  def termToScalaExpr(t: Term, ctx: List[String] = Nil): String =
    exprStr(t, ctx.map(Binder(_, false)), ExtractCtx.empty)

  private def exprStr(t: Term, ctx: List[Binder], e: ExtractCtx): String = t match
    case Term.Var(i) =>
      ctx.lift(i).map(_.name).getOrElse(s"_v$i")

    case Term.App(_, _) =>
      val (head, args) = spine(t, Nil)
      // A *recursive* call is an application of the `Fix` binder, not of a body the
      // global map would recognise, so the self slot has to be resolved here too —
      // otherwise the def declares `[A]` and calls itself with `(A)`.
      val callee = head match
        case Term.Var(i) => ctx.lift(i).filter(_.isSelf).map(_.name)
        case _           => e.defNames.get(head)
      callee match
        case Some(fn) =>
          // A call to a global recursive def: name it instead of pasting its body
          // in, and route the hoisted type arguments into `[...]`.
          val hoisted = e.typeArgs.getOrElse(fn, Set.empty[Int])
          val tArgs   = args.zipWithIndex.collect { case (a, i) if hoisted(i)  => a }
          val vArgs   = args.zipWithIndex.collect { case (a, i) if !hoisted(i) => a }
          val tStr    = if tArgs.isEmpty then ""
                        else s"[${tArgs.map(a => typeStr(a, ctx, e)).mkString(", ")}]"
          s"$fn$tStr${vArgs.map(a => s"(${exprStr(a, ctx, e)})").mkString}"
        case None =>
          val hStr = exprStr(head, ctx, e)
          // `{ … }(x)` and `(y => …)(x)` do not parse as applications in argument
          // position; parenthesising the head makes the application explicit.
          val hRendered = head match
            case Term.Fix(_, _, _) | Term.Lam(_, _, _) |
                 Term.Mat(_, _, _) | Term.Let(_, _, _, _) => s"($hStr)"
            case _                                        => hStr
          s"$hRendered${args.map(a => s"(${exprStr(a, ctx, e)})").mkString}"

    case Term.Lam(x, tp, b) =>
      val safe = sanitizeName(x)
      val bStr = exprStr(b, Binder(safe, isTypeParam(tp)) :: ctx, e)
      s"($safe => $bStr)"

    case Term.Let(x, _, d, b) =>
      val safe = sanitizeName(x)
      val dStr = exprStr(d, ctx, e)
      val bStr = exprStr(b, Binder(safe, false) :: ctx, e)
      s"{ val $safe = $dStr; $bStr }"

    case Term.Pi(x, _, _) =>
      // Pi terms in expression position are types — erase to Any
      "Any"

    case Term.Uni(_) => "()"  // universe in expression position → unit

    case Term.Ind(name, _, _) => name   // reference to inductive type constructor

    case Term.Con(name, indRef, args) =>
      // Builtin constructors are translated to arithmetic literals.
      if e.arithmetic.contains(indRef) then
        extractBuiltinCon(name, indRef, args, ctx, e)
      else
        val ctorName = pascalCase(name)
        val fullName = s"$indRef.$ctorName"
        // Index arguments are erased from the `enum` case; erase them here too.
        val kept = e.ctorDataArgs.get((indRef, name)) match
          case Some(pos) => args.zipWithIndex.collect { case (a, i) if pos.contains(i) => a }
          case None      => args
        if kept.isEmpty then fullName
        else
          val argStrs = kept.map(exprStr(_, ctx, e))
          s"$fullName(${argStrs.mkString(", ")})"

    case Term.Mat(scrutinee, cases, retTpe) =>
      // Check if the scrutinee's type is a builtin inductive.
      val indName = retTpe match
        case Term.Ind(n, _, _) if e.arithmetic.contains(n) => Some(n)
        case _ =>
          // Infer from the first case's ctor owning type when retTpe is opaque.
          cases.headOption.flatMap(mc => e.arithmetic.find(_ => true).filter(_ =>
            // crude: if ANY case ctor is from a builtin, treat as builtin match
            cases.forall(c => List("zero","pos","neg").contains(c.ctor))
          ))
      indName match
        case Some(ind) => extractBuiltinMatch(scrutinee, cases, ind, ctx, e)
        case None      => extractMatch(scrutinee, cases, ctx, e)

    case Term.Fix(name, fixTpe, body) =>
      // An unapplied reference to a global recursive def — name it.
      e.defNames.get(t) match
        case Some(fn) => fn
        case None     =>
          // A genuinely local fixpoint: a block that defines and returns itself.
          val safe    = sanitizeName(name)
          val bodyStr = exprStr(body, Binder(safe, false) :: ctx, e)
          s"{ def $safe: ${typeStr(fixTpe, ctx, e)} = $bodyStr; $safe }"

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
    ctx:    List[Binder],
    e:      ExtractCtx,
  ): String = (indRef, name) match
    case ("Int", "zero")          => "0"
    case ("Int", "pos") if args.size == 1 =>
      val n = exprStr(args.head, ctx, e)
      s"$n + 1"
    case ("Int", "neg") if args.size == 1 =>
      val n = exprStr(args.head, ctx, e)
      s"-($n + 1)"
    case _ =>
      // Fallback: emit as normal constructor
      val ctorName = pascalCase(name)
      val fullName = s"$indRef.$ctorName"
      if args.isEmpty then fullName
      else s"$fullName(${args.map(exprStr(_, ctx, e)).mkString(", ")})"

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
    cases:     List[sroof.core.MatchCase],
    ind:       String,
    ctx:       List[Binder],
    e:         ExtractCtx,
  ): String =
    val sStr = exprStr(scrutinee, ctx, e)
    // Partition cases by ctor name (order-insensitive)
    val byName = cases.map(mc => mc.ctor -> mc).toMap
    def arm(mc: sroof.core.MatchCase, binder: String => String): String =
      if mc.bindings == 0 then exprStr(mc.body, ctx, e)
      else
        val bindName  = s"_n"
        val extCtx    = Binder(bindName, false) :: ctx
        val bodyStr   = exprStr(mc.body, extCtx, e)
        s"{ val $bindName = ${binder(sStr)}; $bodyStr }"

    (byName.get("zero"), byName.get("pos"), byName.get("neg")) match
      case (Some(z), Some(p), Some(n)) =>
        val zBody = exprStr(z.body, ctx, e)
        val pBody = arm(p, s => s"$s - 1")
        val nBody = arm(n, s => s"-$s - 1")
        s"(if ($sStr == 0) $zBody else if ($sStr > 0) $pBody else $nBody)"
      case _ =>
        // Fallback to normal match if case structure is unexpected
        extractMatch(scrutinee, cases, ctx, e)

  /** Render a match expression. */
  private def extractMatch(
    scrutinee: Term,
    cases:     List[sroof.core.MatchCase],
    ctx:       List[Binder],
    e:         ExtractCtx,
  ): String =
    val sStr = exprStr(scrutinee, ctx, e)
    val scrutInd = scrutinee match
      case Term.Var(i) => ctx.lift(i).flatMap(_.ind)
      case other       => headInductive(other)
    if cases.isEmpty then s"($sStr match {})"
    else
      val caseStrs = cases.map { mc =>
        // `bindNames` is in declaration order; the context is its reverse, because
        // the last constructor argument is the innermost binder (`Var(0)`).
        val all       = (0 until mc.bindings).toList.map(i => s"_arg${mc.bindings - 1 - i}")
        val keep      = e.ctorArgsByName.getOrElse(mc.ctor, all.indices.toList)
        // An erased argument keeps its slot in the context — the body still counts
        // binders — but is renamed so that a body which actually uses one fails to
        // compile by name, instead of silently binding the wrong pattern variable.
        val bindNames = all.zipWithIndex.map((n, i) => if keep.contains(i) then n else s"_erased$i")
        val extCtx    = bindNames.reverse.map(Binder(_, false)) ++ ctx
        val bodyStr   = exprStr(mc.body, extCtx, e)
        val patNames  = keep.filter(_ < all.length).map(bindNames)
        // Qualify the pattern when the owner is known: with several enums in scope
        // by wildcard import, a bare `Mk` can be ambiguous.  One unambiguous case
        // name identifies the inductive for the whole match, since a `Mat`'s cases
        // all belong to one.
        val owner     = scrutInd.orElse(cases.flatMap(c => e.ctorOwner.get(c.ctor)).headOption)
        val ctorName  = owner.fold("")(_ + ".") + pascalCase(mc.ctor)
        // `case _.Zero` is not Scala: `_` is not a stable identifier.  The
        // constructors are brought into scope by the `import <Enum>.*` that
        // `extractProgram` emits after each enum, so the bare name resolves.
        if patNames.isEmpty then
          s"    case $ctorName => $bodyStr"
        else
          s"    case $ctorName(${patNames.mkString(", ")}) => $bodyStr"
      }
      s"($sStr match {\n${caseStrs.mkString("\n")}\n  })"

  /** Extract a constructor's Scala `case` line for an enum.
   *
   *  Constructor argument names are generated as `arg0`, `arg1`, etc. (after index erasure).
   *  Index args — those whose type equals one of `indDef.indices[i].tpe` — are erased entirely.
   *  Remaining data arg types are resolved using `allParamNames` for Var references.
   *
   *  `allParamNames` mirrors the De Bruijn nameEnv used during elaboration of ctor arg types:
   *    (params ++ indices).map(_.name).reverse
   *  meaning the innermost index param has De Bruijn index 0, then the type params follow.
   *
   *  Example for Vec.cons(m: Nat, head: A, tail: Vec(A, m)):
   *    indDef.params  = [A: Type], indices = [n: Nat]
   *    allParamNames  = ["n", "A"]   (index n = Var(0), type param A = Var(1))
   *    indexTypes     = {Ind("Nat")} → Nat-typed arg m is erased
   *    result: case Cons(arg0: A, arg1: Vec[A])
   */
  private def extractCtor(
    indDef:         IndDef,
    ctor:           CtorDef,
    typeParamNames: List[String],
    outerCtx:       ExtractCtx,
  ): String =
    val ctorName = pascalCase(ctor.name)
    // The nameEnv `elabInductive` used, as binders: (params ++ indices).reverse, with
    // the constructor's own earlier arguments stacked on top. Those arguments were
    // missing before, so `Sigma.mk(a: A, b: B(a))` resolved `b`'s type one slot off
    // and emitted `A[B]`.  Only `Type`-valued parameters are usable as Scala types;
    // an index or a preceding argument mentioned in a type is a dependency Scala
    // cannot state, and becomes `Any`.
    val outer: List[Binder] =
      (indDef.params ++ indDef.indices).reverse.map(p => Binder(p.name, isTypeParam(p.tpe)))
    val keep  = dataArgPositions(indDef, ctor, outerCtx.knownInds)
    val ectx  = outerCtx.copy(
      indArity = outerCtx.indArity + (indDef.name -> typeParamNames.length))
    if keep.isEmpty then s"case $ctorName"
    else
      val args = keep.zipWithIndex.map { (pos, i) =>
        val scope = List.fill(pos)(Binder("_", false)) ++ outer
        s"arg$i: ${typeStr(ctor.argTpes(pos), scope, ectx)}"
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
    params: List[DefParam],
  ): (List[DefParam], Term, Term) = (body, tpe) match
    // The parameter's type is taken from the *declared* `Pi`, not from the `Lam`.
    // Both describe the same parameter, but the `Lam` copy is stated inside the
    // body's scope — which, for a recursive def, has the `Fix` binder underneath
    // it and so is one slot off from the signature being rendered.
    case (Term.Lam(x, _, b), Term.Pi(_, dom, cod)) =>
      peelLambdas(b, cod, params :+ DefParam(sanitizeName(x), dom, isTypeParam(dom)))
    case (Term.Lam(x, paramTpe, b), _) =>
      peelLambdas(b, tpe, params :+ DefParam(sanitizeName(x), paramTpe, isTypeParam(paramTpe)))
    case _ =>
      (params, tpe, body)

  /** Convert a sroof name to PascalCase for enum case names.
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

  /** Detect the default IO script shape used by stdlib/Effect.sroof. */
  private def hasDefaultIoShape(env: GlobalEnv): Boolean =
    env.lookupInd("IO") match
      case None => false
      case Some(ioDef) =>
        val names = ioDef.ctors.map(_.name).toSet
        names == Set("pure", "read_int", "print_int", "bind")

  /** Runtime interpreter for extracted IO scripts.
   *
   *  Kept outside the kernel and generated only when IO is present.
   */
  private def extractIoRuntime: String =
    """|object IORuntime:
       |  def run(script: IO): Int =
       |    runWith(
       |      script,
       |      () =>
       |        scala.io.StdIn.readLine() match
       |          case null => 0
       |          case s    => s.trim.toInt,
       |      (value: Int) => println(value),
       |    )
       |
       |  def runWith(
       |    script:   IO,
       |    readInt:  () => Int,
       |    printInt: Int => Unit,
       |  ): Int =
       |    script match
       |      case IO.Pure(value) =>
       |        value
       |      case IO.Read_int =>
       |        readInt()
       |      case IO.Print_int(value) =>
       |        printInt(value)
       |        value
       |      case IO.Bind(action, k) =>
       |        val result = runWith(action, readInt, printInt)
       |        runWith(k(result), readInt, printInt)
       |
       |  final case class Trace(
       |    result:          Int,
       |    consumedInputs:  List[Int],
       |    printedValues:   List[Int],
       |    remainingInputs: List[Int],
       |  )
       |
       |  def runWithTrace(script: IO, inputs: List[Int]): Trace =
       |    def eval(
       |      current:    IO,
       |      remaining:  List[Int],
       |      consumedRv: List[Int],
       |      printedRv:  List[Int],
       |    ): (Int, List[Int], List[Int], List[Int]) =
       |      current match
       |        case IO.Pure(value) =>
       |          (value, remaining, consumedRv, printedRv)
       |        case IO.Read_int =>
       |          remaining match
       |            case x :: rest => (x, rest, x :: consumedRv, printedRv)
       |            case Nil       => (0, Nil, consumedRv, printedRv)
       |        case IO.Print_int(value) =>
       |          (value, remaining, consumedRv, value :: printedRv)
       |        case IO.Bind(action, k) =>
       |          val (v, rem1, con1, out1) = eval(action, remaining, consumedRv, printedRv)
       |          eval(k(v), rem1, con1, out1)
       |
       |    val (result, remaining, consumedRv, printedRv) = eval(script, inputs, Nil, Nil)
       |    Trace(result, consumedRv.reverse, printedRv.reverse, remaining)
       |""".stripMargin
