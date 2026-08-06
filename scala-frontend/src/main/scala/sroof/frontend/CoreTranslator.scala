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
    val ctors = ind.ctors.map { ctor =>
      val fields = ctor.fields.map { f =>
        f.tpe match
          case ResolvedType.Inductive(_, name) => Term.Ind(name, Nil, Nil)
      }
      CtorDef(ctor.name, fields)
    }
    PositivityChecker
      .check(ind.name, ctors)
      .left.map(msg => FrontendError.enumError(ind.name, s"is not strictly positive: $msg", ind.span))
      .map(_ => IndDef(name = ind.name, params = Nil, ctors = ctors, universe = 0))

  // ---- Types ----

  def translateType(
    tpe:     ResolvedType,
    env:     TranslationEnv,
    subject: String,
    span:    SourceSpan,
  ): Either[FrontendError, Term] =
    tpe match
      case ResolvedType.Inductive(id, name) =>
        if env.inductives.contains(id) then Right(Term.Ind(name, Nil, Nil))
        else Left(FrontendError.defError(subject,
          s"type '$name' is not an inductive type declared in this proof module", span))

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
    case ResolvedExpr.Call(target, _, args, _)      => args.flatMap(directCalls).toSet + target
    case ResolvedExpr.Construct(_, _, _, args, _)   => args.flatMap(directCalls).toSet
    case ResolvedExpr.Match(scrut, cases, _)        =>
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
    for
      paramTpes <- rd.params.foldLeft[Either[FrontendError, List[Term]]](Right(Nil)) { (acc, p) =>
                     for
                       ts <- acc
                       t  <- translateType(p.tpe, env, rd.name, rd.span)
                     yield ts :+ t
                   }
      resultTpe <- translateType(rd.result, env, rd.name, rd.span)
      fullTpe    = rd.params.zip(paramTpes).foldRight(resultTpe) { case ((p, t), cod) =>
                     Term.Pi(p.name, t, cod)
                   }
      // Parameters enter the scope reversed: the last parameter is Var(0).
      bodyTerm  <- translateExpr(rd.body, resultTpe, rd.params.reverse.map(_.id),
                                 Some(rd.id), env, rd.name)
      lams       = rd.params.zip(paramTpes).foldRight(bodyTerm) { case ((p, t), acc) =>
                     Term.Lam(p.name, t, acc)
                   }
      fixTerm    = Term.Fix(rd.name, fullTpe, lams)
      _         <- checkTermination(rd, fixTerm, env)
    yield DefEntry(rd.name, fullTpe, fixTerm)

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

      case ResolvedExpr.Call(target, name, args, span) =>
        for
          sig <- env.defSigs.get(target).toRight(FrontendError.defError(subject,
                   s"call to '$name', which is not a verified definition in this proof module", span))
          _   <- if sig.params.length == args.length then Right(())
                 else Left(FrontendError.defError(subject,
                   s"call to '$name' expects ${sig.params.length} argument(s) but got ${args.length}", span))
          // Self-recursion points at the Fix binder, one past the innermost scope.
          // Any other call is inlined: core `Term` has no global-reference node,
          // and a translated def body is closed, so it needs no shifting.
          fn  <- if self.contains(target) then Right(Term.Var(scope.length))
                 else env.defs.get(target).map(_.body).toRight(FrontendError.defError(subject,
                   s"'$name' is called before it has been translated (internal ordering error)", span))
          argTerms <- translateArgs(args, sig.params.map(_.tpe), scope, self, env, subject, span)
        yield argTerms.foldLeft(fn)(Term.App.apply)

      case ResolvedExpr.Construct(_, ctorId, ctorName, args, span) =>
        for
          pair <- env.ctors.get(ctorId).toRight(FrontendError.defError(subject,
                    s"'$ctorName' is not a constructor of an inductive type in this proof module", span))
          (ind, ctor) = pair
          _    <- if ctor.fields.length == args.length then Right(())
                  else Left(FrontendError.defError(subject,
                    s"constructor '$ctorName' expects ${ctor.fields.length} field(s) but got ${args.length}", span))
          argTerms <- translateArgs(args, ctor.fields.map(_.tpe), scope, self, env, subject, span)
        yield Term.Con(ctor.name, ind.name, argTerms)

      case ResolvedExpr.Match(scrut, cases, span) =>
        for
          _        <- if cases.nonEmpty then Right(())
                      else Left(FrontendError.defError(subject, "match has no branches", span))
          indPair  <- env.ctors.get(cases.head.ctor).toRight(FrontendError.defError(subject,
                        s"'${cases.head.ctorName}' is not a constructor of an inductive type", span))
          ind       = indPair._1
          _        <- checkExhaustive(ind, cases, subject, span)
          scrutT   <- translateExpr(scrut, Term.Ind(ind.name, Nil, Nil), scope, self, env, subject)
          caseTerms <- cases.foldLeft[Either[FrontendError, List[MatchCase]]](Right(Nil)) { (acc, c) =>
                        for
                          done <- acc
                          // Field binders enter the scope reversed: last field is Var(0).
                          body <- translateExpr(c.body, expected, c.binders.reverse.map(_.id) ++ scope,
                                                self, env, subject)
                        yield done :+ MatchCase(c.ctorName, c.binders.length, body)
                      }
        yield Term.Mat(scrutT, caseTerms, expected)

      case ResolvedExpr.Let(binder, value, body, span) =>
        for
          binderTpe <- translateType(binder.tpe, env, subject, span)
          valueT    <- translateExpr(value, binderTpe, scope, self, env, subject)
          bodyT     <- translateExpr(body, expected, binder.id :: scope, self, env, subject)
        yield Term.Let(binder.name, binderTpe, valueT, bodyT)

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
        expected <- translateType(tpe, env, subject, span)
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
      tpe <- translateType(prop.tpe, env, subject, prop.span)
      lhs <- translateExpr(prop.lhs, tpe, scope, None, env, subject)
      rhs <- translateExpr(prop.rhs, tpe, scope, None, env, subject)
    yield sroof.tactic.Eq.mkPropType(lhs, rhs)

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
  ): Either[FrontendError, (Context, List[Term])] =
    params.foldLeft[Either[FrontendError, (Context, List[Term])]](Right((Context.empty, Nil))) {
      case (acc, p) =>
        for
          state <- acc
          (ctx, tpes) = state
          t <- translateType(p.tpe, env, subject, span)
        yield (ctx.extend(p.name, t), tpes :+ t)
    }
