package sroof.frontend

import sroof.core.{
  Context, CtorDef, DefEntry, GlobalEnv, IndDef, MatchCase, Param,
  PositivityChecker, TerminationChecker, Term,
}

/** Translation from the resolved IR into sroof core terms.
 *
 *  ## Trust
 *
 *  This is the **Scala-to-core semantic bridge**.  `Kernel.verify` decides
 *  whether a proof term inhabits its claimed core proposition, but it cannot
 *  know whether that core proposition says anything about the Scala program the
 *  user wrote.  That correspondence rests on this file, so it is kept small,
 *  total, and conservative: every construct it accepts has one obvious core
 *  reading, and anything else is an error.
 *
 *  ## De Bruijn conventions
 *
 *  A `scope` is the list of binders currently visible, **innermost first**, so
 *  `Var(i)` is `scope(i)`.  This mirrors `syntax.Elaborator`'s `NameEnv` exactly,
 *  which is what makes terms produced here interchangeable with terms produced
 *  by the legacy `.sroof` path.
 *
 *  Two orderings are easy to get backwards, so they are stated once here:
 *
 *  - A definition's parameters enter the scope **reversed**: for `def f(a, b)`
 *    the body is `Lam(a, Lam(b, ...))`, so inside it `b` is `Var(0)` and `a` is
 *    `Var(1)`.
 *  - A match branch's field binders also enter **reversed**: in a branch for
 *    `Succ(k)` with one field, `k` is `Var(0)`; with fields `(x, y)`, `y` is
 *    `Var(0)` and `x` is `Var(1)`.
 *
 *  The self-reference index is `Var(scope.length)`: every definition body is
 *  wrapped in a `Fix` whose binder sits immediately outside all lambdas and all
 *  match binders, so it is always one past the innermost scope.
 *
 *  ## Why no `Meta`
 *
 *  Every type in the supported subset is a closed `Ind(name, Nil, Nil)`.  That
 *  lets the expected type be threaded top-down and used verbatim as a `Mat`
 *  return type — no shifting is ever needed, and no unresolved metavariable is
 *  ever produced.  If that invariant is ever broken by a richer type, the
 *  threading below must start shifting; see `translateExpr`.
 */
object CoreTranslator:

  /** Binders in scope, innermost first.  `Var(i)` refers to `scope(i)`. */
  private type Scope = List[SymbolId]

  /** Everything translation needs to resolve a reference by identity. */
  final case class TranslationEnv(
    inductives: Map[SymbolId, ResolvedInductive],
    /** Constructor id -> (owning inductive, constructor). */
    ctors:      Map[SymbolId, (ResolvedInductive, ResolvedConstructor)],
    /** Signatures of every verified definition in the module. */
    defSigs:    Map[SymbolId, ResolvedDef],
    /** Core entries for definitions translated so far (used for inlining). */
    defs:       Map[SymbolId, DefEntry],
  )

  object TranslationEnv:
    def apply(module: ResolvedModule): TranslationEnv =
      val inductives = module.inductives.map(i => i.id -> i).toMap
      val ctors = (
        for
          ind  <- module.inductives
          ctor <- ind.ctors
        yield ctor.id -> (ind, ctor)
      ).toMap
      TranslationEnv(inductives, ctors, module.definitions.map(d => d.id -> d).toMap, Map.empty)

  // ---- Inductive types ----

  /** Translate a Scala enum into an `IndDef`, preserving constructor order.
   *
   *  Runs the existing strict-positivity check: an enum that Scala accepts can
   *  still be logically unsound as an inductive definition.
   */
  def translateInductive(ind: ResolvedInductive): Either[FrontendError, IndDef] =
    val m = ind.typeParams.length

    // Constructor field types follow the *progressive* De Bruijn convention that
    // `IndChecker.instantiateArgType` defines: inside `argTpes(j)`, `Var(0..j-1)`
    // are the preceding fields and `Var(j..j+m-1)` are the type parameters, with
    // `Var(j)` the **last** parameter.  This is the one place in the frontend
    // that does not use ordinary innermost-first scoping, so it is built by hand
    // rather than routed through `translateType`.
    def fieldType(tpe: ResolvedType, j: Int): Either[FrontendError, Term] =
      tpe match
        case ResolvedType.TypeVar(id, name) =>
          ind.typeParams.indexWhere(_.id == id) match
            case -1 => Left(FrontendError.enumError(ind.name,
              s"field type '$name' is not a type parameter of this enum", ind.span))
            case p  => Right(Term.Var(j + (m - 1 - p)))
        case ResolvedType.Inductive(_, name, args) =>
          args.foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { (acc, a) =>
            for
              done <- acc
              t    <- fieldType(a, j)
            yield done :+ t
          }.map(as => as.foldLeft(Term.Ind(name, Nil, Nil): Term)(Term.App.apply))

    val ctorsE = ind.ctors.foldLeft[Either[FrontendError, List[CtorDef]]](Right(Nil)) { (acc, ctor) =>
      for
        done   <- acc
        fields <- ctor.fields.zipWithIndex
                    .foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) {
                      case (facc, (f, j)) =>
                        for
                          fs <- facc
                          t  <- fieldType(f.tpe, j)
                        yield fs :+ t
                    }
      yield done :+ CtorDef(ctor.name, fields)
    }

    for
      ctors <- ctorsE
      _     <- PositivityChecker.check(ind.name, ctors).left.map(msg =>
                 FrontendError.enumError(ind.name, s"is not strictly positive: $msg", ind.span))
    yield IndDef(
      name     = ind.name,
      params   = ind.typeParams.map(p => Param(p.name, Term.Uni(0))),
      ctors    = ctors,
      universe = 0,
    )

  // ---- Types ----

  /** Translate a type in a scope where type parameters are ordinary binders.
   *
   *  Core has no separate namespace for types: a type parameter is a value
   *  binder of type `Type`, so it is found in the same `scope` as everything
   *  else and referred to by the same De Bruijn index.
   */
  def translateType(
    tpe:     ResolvedType,
    env:     TranslationEnv,
    subject: String,
    span:    SourceSpan,
    scope:   Scope = Nil,
  ): Either[FrontendError, Term] =
    tpe match
      case ResolvedType.TypeVar(id, name) =>
        scope.indexOf(id) match
          case -1 => Left(FrontendError.defError(subject,
            s"type parameter '$name' is not in scope here", span))
          case i  => Right(Term.Var(i))

      case ResolvedType.Inductive(id, name, args) =>
        if !env.inductives.contains(id) then
          Left(FrontendError.defError(subject,
            s"type '$name' is not an inductive type declared in this proof module", span))
        else
          val expected = env.inductives(id).typeParams.length
          if args.length != expected then
            Left(FrontendError.defError(subject,
              s"type '$name' expects $expected type argument(s) but got ${args.length}", span))
          else
            args.foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { (acc, a) =>
              for
                done <- acc
                t    <- translateType(a, env, subject, span, scope)
              yield done :+ t
            }.map(as => as.foldLeft(Term.Ind(name, Nil, Nil): Term)(Term.App.apply))

  // ---- Definitions ----

  /** Order definitions so that each is translated after everything it calls.
   *
   *  Scala lets a method refer to a method declared later in the file, so source
   *  order is not a usable schedule.  Direct self-recursion is fine (it becomes
   *  `Fix`); any cycle involving two or more definitions is mutual recursion,
   *  which the termination checker cannot accept and which is rejected here with
   *  a diagnostic naming the participants.
   */
  def orderDefinitions(module: ResolvedModule): Either[FrontendError, List[ResolvedDef]] =
    val byId   = module.definitions.map(d => d.id -> d).toMap
    val callsOf: Map[SymbolId, Set[SymbolId]] =
      module.definitions.map(d => d.id -> (directCalls(d.body) - d.id).filter(byId.contains)).toMap

    // Iterative Kahn-style scheduling: repeatedly emit definitions whose
    // dependencies are all already emitted.  Whatever is left is in a cycle.
    def loop(
      remaining: List[ResolvedDef],
      emitted:   Set[SymbolId],
      acc:       List[ResolvedDef],
    ): Either[FrontendError, List[ResolvedDef]] =
      if remaining.isEmpty then Right(acc)
      else
        val (ready, blocked) = remaining.partition(d => callsOf(d.id).forall(emitted.contains))
        if ready.isEmpty then
          val names = blocked.map(_.name).sorted.mkString(", ")
          Left(FrontendError.defError(blocked.head.name,
            s"mutual recursion is not supported (cycle among: $names); " +
            "only direct self-recursion accepted by the termination checker is allowed",
            blocked.head.span))
        else loop(blocked, emitted ++ ready.map(_.id), acc ++ ready)

    loop(module.definitions, Set.empty, Nil)

  private def directCalls(e: ResolvedExpr): Set[SymbolId] = e match
    case ResolvedExpr.Local(_, _, _)                => Set.empty
    case ResolvedExpr.Call(target, _, args, _, _)   => args.flatMap(directCalls).toSet + target
    case ResolvedExpr.Construct(_, _, _, args, _, _) => args.flatMap(directCalls).toSet
    case ResolvedExpr.Match(scrut, cases, _, _)    =>
      directCalls(scrut) ++ cases.flatMap(c => directCalls(c.body))
    case ResolvedExpr.Let(_, value, body, _)        => directCalls(value) ++ directCalls(body)

  /** Translate one definition into a `DefEntry`, running the termination check.
   *
   *  The body is always `Fix`-wrapped, recursive or not, matching what the
   *  legacy elaborator produces for `def`s.
   */
  def translateDef(
    rd:  ResolvedDef,
    env: TranslationEnv,
  ): Either[FrontendError, DefEntry] =
    // Type parameters become leading `Type`-valued value parameters, so the whole
    // signature is one curried chain and the body's scope is `(tparams ++ params)`
    // reversed, exactly as for an ordinary definition.
    val allParams = rd.typeParams ++ rd.params
    val scopeAt   = (i: Int) => allParams.take(i).reverse.map(_.id)
    for
      paramTpes <- allParams.zipWithIndex
                     .foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) {
                       case (acc, (p, i)) =>
                         for
                           ts <- acc
                           t  <- if rd.typeParams.contains(p) then Right(Term.Uni(0))
                                 else translateType(p.tpe, env, rd.name, rd.span, scopeAt(i))
                         yield ts :+ t
                     }
      fullScope  = allParams.reverse.map(_.id)
      resultTpe <- translateType(rd.result, env, rd.name, rd.span, fullScope)
      fullTpe    = allParams.zip(paramTpes).foldRight(resultTpe) { case ((p, t), cod) =>
                     Term.Pi(p.name, t, cod)
                   }
      // Parameters enter the scope reversed: the last parameter is Var(0).
      bodyTerm  <- translateExpr(rd.body, resultTpe, fullScope, Some(rd.id), env, rd.name)
      entry     <- assemble(rd, fullTpe, paramTpes, bodyTerm, env, allParams)
    yield entry

  /** Wrap a translated body into its `DefEntry`.
   *
   *  A definition with no parameters is **not** `Fix`-wrapped, matching the
   *  legacy elaborator.  A nullary `Fix` could never reduce: it only unfolds when
   *  applied, and there is nothing to apply it to, so it would sit unevaluated
   *  wherever it was inlined.  That also removes the binder a self-reference
   *  would point at, so nullary recursion is rejected rather than left dangling.
   */
  private def assemble(
    rd:        ResolvedDef,
    fullTpe:   Term,
    paramTpes: List[Term],
    bodyTerm:  Term,
    env:       TranslationEnv,
    allParams: List[ResolvedBinder],
  ): Either[FrontendError, DefEntry] =
    if allParams.isEmpty then
      if directCalls(rd.body).contains(rd.id) then
        Left(FrontendError.defError(rd.name,
          "a definition with no parameters cannot be recursive: there is no argument " +
          "for the recursion to decrease on", rd.span))
      else Right(DefEntry(rd.name, fullTpe, bodyTerm))
    else
      val lams = allParams.zip(paramTpes).foldRight(bodyTerm) { case ((p, t), acc) =>
        Term.Lam(p.name, t, acc)
      }
      val fixTerm = Term.Fix(rd.name, fullTpe, lams)
      checkTermination(rd, fixTerm, env).map(_ => DefEntry(rd.name, fullTpe, fixTerm))

  private def checkTermination(
    rd:  ResolvedDef,
    fix: Term,
    env: TranslationEnv,
  ): Either[FrontendError, Unit] =
    given GlobalEnv = GlobalEnv.empty
    TerminationChecker.check(fix).left.map { msg =>
      FrontendError.defError(rd.name,
        s"recursion is not structurally decreasing: $msg", rd.span)
    }

  // ---- Expressions ----

  /** Translate an expression that must have core type `expected`.
   *
   *  `expected` is used verbatim as the return type of any `Mat` produced here.
   *  That is only sound because every supported type is closed, so it needs no
   *  De Bruijn shifting when passed under a binder.  Widening the type language
   *  means revisiting every recursive call below.
   */
  def translateExpr(
    e:        ResolvedExpr,
    expected: Term,
    scope:    Scope,
    self:     Option[SymbolId],
    env:      TranslationEnv,
    subject:  String,
  ): Either[FrontendError, Term] =
    e match
      case ResolvedExpr.Local(id, name, span) =>
        scope.indexOf(id) match
          case -1 => Left(FrontendError.defError(subject,
            s"'$name' is not a parameter or pattern binder of this definition", span))
          case i  => Right(Term.Var(i))

      case ResolvedExpr.Call(target, name, args, span, typeArgs) =>
        for
          sig <- env.defSigs.get(target).toRight(FrontendError.defError(subject,
                   s"call to '$name', which is not a verified definition in this proof module", span))
          _   <- if sig.params.length == args.length then Right(())
                 else Left(FrontendError.defError(subject,
                   s"call to '$name' expects ${sig.params.length} argument(s) but got ${args.length}", span))
          _   <- if sig.typeParams.length == typeArgs.length then Right(())
                 else Left(FrontendError.defError(subject,
                   s"call to '$name' expects ${sig.typeParams.length} type argument(s) but got " +
                   s"${typeArgs.length}", span))
          // Self-recursion points at the Fix binder, one past the innermost scope.
          // Any other call is inlined: core `Term` has no global-reference node,
          // and a translated def body is closed, so it needs no shifting.
          fn  <- if self.contains(target) then Right(Term.Var(scope.length))
                 else env.defs.get(target).map(_.body).toRight(FrontendError.defError(subject,
                   s"'$name' is called before it has been translated (internal ordering error)", span))
          // The callee's parameter types are stated in its own type parameters;
          // instantiate them at this call's type arguments before checking the
          // value arguments against them.
          subst     = sig.typeParams.map(_.id).zip(typeArgs).toMap
          typeTerms <- typeArgs.foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { (acc, t) =>
                         for
                           done <- acc
                           term <- translateType(t, env, subject, span, scope)
                         yield done :+ term
                       }
          argTerms  <- translateArgs(args, sig.params.map(p => substTypes(p.tpe, subst)),
                                     scope, self, env, subject, span)
        yield (typeTerms ++ argTerms).foldLeft(fn)(Term.App.apply)

      case ResolvedExpr.Construct(_, ctorId, ctorName, args, span, typeArgs) =>
        for
          pair <- env.ctors.get(ctorId).toRight(FrontendError.defError(subject,
                    s"'$ctorName' is not a constructor of an inductive type in this proof module", span))
          (ind, ctor) = pair
          _    <- if ctor.fields.length == args.length then Right(())
                  else Left(FrontendError.defError(subject,
                    s"constructor '$ctorName' expects ${ctor.fields.length} field(s) but got ${args.length}", span))
          // `Term.Con` carries only value arguments; the checker recovers the
          // type arguments from the expected type.  They are still needed here to
          // instantiate the field types the arguments are checked against.
          subst     = ind.typeParams.map(_.id).zip(typeArgs).toMap
          argTerms <- translateArgs(args, ctor.fields.map(f => substTypes(f.tpe, subst)),
                                    scope, self, env, subject, span)
        yield Term.Con(ctor.name, ind.name, argTerms)

      case ResolvedExpr.Match(scrut, cases, span, scrutTpe) =>
        for
          _        <- if cases.nonEmpty then Right(())
                      else Left(FrontendError.defError(subject, "match has no branches", span))
          indPair  <- env.ctors.get(cases.head.ctor).toRight(FrontendError.defError(subject,
                        s"'${cases.head.ctorName}' is not a constructor of an inductive type", span))
          ind       = indPair._1
          _        <- checkExhaustive(ind, cases, subject, span)
          scrutCore <- translateType(scrutTpe, env, subject, span, scope)
          scrutT   <- translateExpr(scrut, scrutCore, scope, self, env, subject)
          caseTerms <- cases.foldLeft[Either[FrontendError, List[MatchCase]]](Right(Nil)) { (acc, c) =>
                        for
                          done <- acc
                          // Field binders enter the scope reversed: last field is Var(0).
                          // `expected` is a *type*, so it must move up past the
                          // binders this branch introduces.
                          body <- translateExpr(c.body,
                                                sroof.core.Subst.shift(c.binders.length, expected),
                                                c.binders.reverse.map(_.id) ++ scope,
                                                self, env, subject)
                        yield done :+ MatchCase(c.ctorName, c.binders.length, body)
                      }
        yield Term.Mat(scrutT, caseTerms, expected)

      case ResolvedExpr.Let(binder, value, body, span) =>
        for
          binderTpe <- translateType(binder.tpe, env, subject, span, scope)
          valueT    <- translateExpr(value, binderTpe, scope, self, env, subject)
          bodyT     <- translateExpr(body, sroof.core.Subst.shift(1, expected),
                                     binder.id :: scope, self, env, subject)
        yield Term.Let(binder.name, binderTpe, valueT, bodyT)

  /** Instantiate type parameters at their actual arguments. */
  private def substTypes(tpe: ResolvedType, subst: Map[SymbolId, ResolvedType]): ResolvedType =
    tpe match
      case ResolvedType.TypeVar(id, _)            => subst.getOrElse(id, tpe)
      case ResolvedType.Inductive(id, name, args) =>
        ResolvedType.Inductive(id, name, args.map(substTypes(_, subst)))

  private def translateArgs(
    args:     List[ResolvedExpr],
    tpes:     List[ResolvedType],
    scope:    Scope,
    self:     Option[SymbolId],
    env:      TranslationEnv,
    subject:  String,
    span:     SourceSpan,
  ): Either[FrontendError, List[Term]] =
    args.zip(tpes).foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { case (acc, (arg, tpe)) =>
      for
        done     <- acc
        expected <- translateType(tpe, env, subject, span, scope)
        term     <- translateExpr(arg, expected, scope, self, env, subject)
      yield done :+ term
    }

  /** Every constructor covered exactly once, in the inductive's declared order.
   *
   *  Scala's own exhaustivity check is not enough: the branches must also line up
   *  positionally with `IndDef.ctors`, because `Term.Mat` matches branches to
   *  constructors by position in the existing checker.
   */
  private def checkExhaustive(
    ind:     ResolvedInductive,
    cases:   List[ResolvedCase],
    subject: String,
    span:    SourceSpan,
  ): Either[FrontendError, Unit] =
    val covered = cases.map(_.ctor)
    val missing = ind.ctors.filterNot(c => covered.contains(c.id)).map(_.name)
    val dups    = covered.groupBy(identity).filter(_._2.length > 1).keys
                    .flatMap(id => ind.ctors.find(_.id == id).map(_.name)).toList.sorted
    if missing.nonEmpty then
      Left(FrontendError.defError(subject,
        s"match on ${ind.name} is missing branch(es) for: ${missing.mkString(", ")}", span))
    else if dups.nonEmpty then
      Left(FrontendError.defError(subject,
        s"match on ${ind.name} has duplicate branch(es) for: ${dups.mkString(", ")}", span))
    else Right(())

  /** Reorder match branches into the inductive's constructor order. */
  def normaliseCaseOrder(
    ind:   ResolvedInductive,
    cases: List[ResolvedCase],
  ): List[ResolvedCase] =
    ind.ctors.flatMap(c => cases.find(_.ctor == c.id))

  /** Reorder tactic branches into the inductive's constructor order. */
  def normaliseTacticCaseOrder(
    ind:   ResolvedInductive,
    cases: List[ResolvedTacticCase],
  ): List[ResolvedTacticCase] =
    ind.ctors.flatMap(c => cases.find(_.ctor == c.id))

  // ---- Propositions ----

  /** Translate an equality goal into the `Eq` encoding the tactics and kernel use.
   *
   *  The 2-arg form is deliberate, not a shortcut: it is the encoding the
   *  existing checker can type and the one `Builtins`/`Kernel` are written
   *  against.  The element type is still translated, because it is what the
   *  two sides are checked against.
   */
  def translateProp(
    prop:    ResolvedProp,
    scope:   Scope,
    env:     TranslationEnv,
    subject: String,
  ): Either[FrontendError, Term] =
    for
      tpe <- translateType(prop.tpe, env, subject, prop.span, scope)
      lhs <- translateExpr(prop.lhs, tpe, scope, None, env, subject)
      rhs <- translateExpr(prop.rhs, tpe, scope, None, env, subject)
    yield sroof.tactic.Eq.mkPropType(lhs, rhs)

  /** Translate an expression against a proof context built by the tactic engine.
   *
   *  Unlike [[translateExpr]], locals are resolved **by name**, because the
   *  contexts `Builtins` builds for induction branches are named, not tracked by
   *  compiler symbol — the engine addresses them the same way. Shadowing
   *  resolves innermost-first, which is what Scala means too.
   *
   *  Deliberately narrow: only variables, constructor applications, and calls to
   *  verified definitions. A `match` or `let` here would need an expected type to
   *  thread, and nothing in the supported tactics requires one.
   */
  def translateInProofContext(
    e:       ResolvedExpr,
    ctx:     Context,
    env:     TranslationEnv,
    subject: String,
  ): Either[FrontendError, Term] =
    e match
      case ResolvedExpr.Local(_, name, span) =>
        ctx.entries.indexWhere(_.name == name) match
          case -1 => Left(FrontendError.tacticError(subject,
            s"'$name' is not in scope at this point in the proof", span))
          case i  => Right(Term.Var(i))

      case ResolvedExpr.Construct(_, ctorId, ctorName, args, span, _) =>
        for
          pair <- env.ctors.get(ctorId).toRight(FrontendError.tacticError(subject,
                    s"'$ctorName' is not a constructor of this proof module", span))
          (ind, ctor) = pair
          terms <- args.foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { (acc, a) =>
                     for
                       done <- acc
                       t    <- translateInProofContext(a, ctx, env, subject)
                     yield done :+ t
                   }
        yield Term.Con(ctor.name, ind.name, terms)

      case ResolvedExpr.Call(target, name, args, span, typeArgs) =>
        for
          entry <- env.defs.get(target).toRight(FrontendError.tacticError(subject,
                     s"'$name' is not a verified definition of this proof module", span))
          terms <- args.foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { (acc, a) =>
                     for
                       done <- acc
                       t    <- translateInProofContext(a, ctx, env, subject)
                     yield done :+ t
                   }
        yield terms.foldLeft(entry.body)(Term.App.apply)

      case other =>
        Left(FrontendError.tacticError(subject,
          "only variables, constructor applications, and calls may be used here", other.span))

  /** The proof context and full `Pi` proposition for a theorem's parameters.
   *
   *  Mirrors `cli.Checker`: parameters are added to the context left to right,
   *  so the last parameter is `Var(0)`, and the goal is elaborated in the
   *  reversed scope.
   */
  def theoremContext(
    params:  List[ResolvedBinder],
    env:     TranslationEnv,
    subject: String,
    span:    SourceSpan,
    typeParams: List[ResolvedBinder] = Nil,
  ): Either[FrontendError, (Context, List[Term])] =
    // Type parameters are quantified ahead of the value parameters and become
    // ordinary `Type`-valued binders, so they enter the context first.
    val all = typeParams ++ params
    all.zipWithIndex.foldLeft[Either[FrontendError, (Context, List[Term])]](
      Right((Context.empty, Nil))
    ) {
      case (acc, (p, i)) =>
        for
          state <- acc
          (ctx, tpes) = state
          scope = all.take(i).reverse.map(_.id)
          t <- if typeParams.contains(p) then Right(Term.Uni(0))
               else translateType(p.tpe, env, subject, span, scope)
        yield (ctx.extend(p.name, t), tpes :+ t)
    }
