package sroof.plugin.dotc

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.NameOps.stripModuleClassSuffix
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.Types.Type

import sroof.frontend.*

/** Converts typed dotc trees into the compiler-independent frontend IR.
 *
 *  This is the only place in sroof that knows what a dotc tree looks like.
 *  Everything it produces is `sroof.frontend` IR, so the translation, proof, and
 *  kernel layers stay portable across compiler versions.
 *
 *  Two rules are enforced throughout:
 *
 *  - **Identity, not spelling.** Every DSL call, constructor, and definition is
 *    recognised by comparing resolved `Symbol`s.  Binders are tracked by symbol
 *    too; names ride along only for diagnostics and core binder labels.
 *  - **Fail closed.** No branch turns an unrecognised tree into an IR node.
 *    Anything outside the documented subset becomes a [[FrontendError]] carrying
 *    a source position.
 */
final class TreeExtractor(dsl: DslSymbols)(using Context):
  import tpd.*
  import ExtractorSupport.*

  def isProofModule(sym: Symbol): Boolean =
    sym.isClass && annotationsOf(sym).contains(dsl.proofModuleAnnot)

  def isTheorem(sym: Symbol): Boolean = annotationsOf(sym).contains(dsl.theoremAnnot)

  // ================================================================
  // Module
  // ================================================================

  def extractModule(moduleClass: TypeDef): Either[FrontendError, ResolvedModule] =
    val sym  = moduleClass.symbol
    val name = sym.sourceModule.orElse(sym).name.stripModuleClassSuffix.toString
    val span = spanOf(moduleClass)

    moduleClass.rhs match
      case tmpl: Template =>
        for
          inductives <- InductiveExtractor.extract(tmpl.body)
          _          <- rejectUnsupportedMembers(tmpl.body, name)
          sigs       <- extractSignatures(tmpl.body, inductives)
          defs       <- extractDefinitions(tmpl.body, inductives, sigs)
          theorems   <- extractTheorems(tmpl.body, inductives, sigs)
        yield ResolvedModule(idOf(sym), name, inductives.all, defs, theorems, span)
      case _ =>
        Left(FrontendError.moduleError(FrontendStage.TheoremExtraction,
          s"@proofModule $name has no template body", span))

  // ================================================================
  // Member policing
  // ================================================================

  /** Reject module members outside the verified subset.
   *
   *  Everything a `@proofModule` declares is verified code, so a field, a `var`,
   *  or a nested class must fail rather than be quietly ignored: an ignored
   *  `var` would let effectful code sit next to a proof and look verified.
   */
  private def rejectUnsupportedMembers(
    body:       List[Tree],
    moduleName: String,
  ): Either[FrontendError, Unit] =
    body.foldLeft[Either[FrontendError, Unit]](Right(())) { (acc, tree) =>
      acc.flatMap { _ =>
        val sym = tree.symbol
        if sym.is(Flags.Synthetic) || sym.is(Flags.Artifact) then Right(())
        else tree match
          case td: TypeDef if td.symbol.is(Flags.Module) || td.symbol.is(Flags.Enum) => Right(())
          case vd: ValDef if vd.symbol.is(Flags.Module)                              => Right(())
          case dd: DefDef if dd.symbol.isConstructor                                 => Right(())
          case _: DefDef                                                             => Right(())
          case vd: ValDef =>
            val what = if vd.symbol.is(Flags.Mutable) then "a mutable field (var)" else "a field (val)"
            Left(FrontendError.moduleError(FrontendStage.DefinitionTranslation,
              s"@proofModule $moduleName declares $what '${vd.name}'; " +
              "verified modules may only declare enums, defs, and @theorem defs", spanOf(vd)))
          case td: TypeDef =>
            Left(FrontendError.moduleError(FrontendStage.DefinitionTranslation,
              s"@proofModule $moduleName declares '${td.name}', which is not an enum; " +
              "classes, traits, and type aliases are not supported as verified data", spanOf(td)))
          case _ => Right(())
      }
    }

  // ================================================================
  // Definitions
  // ================================================================

  private final case class DefSignature(
    params:      List[ResolvedBinder],
    result:      ResolvedType,
    binderScope: Map[Symbol, ResolvedBinder],
  )

  private def isVerifiedDef(sym: Symbol): Boolean =
    !sym.isConstructor &&
    !sym.is(Flags.Synthetic) &&
    !sym.is(Flags.Artifact) &&
    !sym.is(Flags.Accessor) &&
    !isTheorem(sym)

  /** Signatures are collected before bodies: Scala lets a method call one that is
   *  declared later in the file.
   */
  private def extractSignatures(
    body:  List[Tree],
    index: InductiveIndex,
  ): Either[FrontendError, Map[Symbol, DefSignature]] =
    val all = body.collect {
      case dd: DefDef if isVerifiedDef(dd.symbol) || isTheorem(dd.symbol) => dd
    }
    all.foldLeft[Either[FrontendError, Map[Symbol, DefSignature]]](Right(Map.empty)) { (acc, dd) =>
      for
        done <- acc
        sig  <- extractSignature(dd, index, isTheorem(dd.symbol))
      yield done + (dd.symbol -> sig)
    }

  private def extractSignature(
    dd:         DefDef,
    index:      InductiveIndex,
    theoremDef: Boolean,
  ): Either[FrontendError, DefSignature] =
    val name = dd.symbol.name.toString
    val span = spanOf(dd)
    if dd.leadingTypeParams.nonEmpty then
      Left(FrontendError.defError(name, "type parameters are not supported", span))
    else
      // Curried parameter lists are flattened: core types are curried anyway, so
      // `f(a: A)(b: B)` and `f(a: A, b: B)` produce the same `Pi(a, A, Pi(b, B, _))`.
      // Call sites are matched against the flattened arity, and a partial
      // application is rejected there rather than silently accepted here.
      val params = dd.termParamss.flatten
      for
        binders <- params.foldLeft[Either[FrontendError, List[ResolvedBinder]]](Right(Nil)) { (acc, vd) =>
                     for
                       done <- acc
                       t    <- resolveDeclaredType(vd.tpt.tpe, index, name, spanOf(vd))
                     yield done :+ ResolvedBinder(idOf(vd.symbol), vd.name.toString, t)
                   }
        // A theorem's result type is the DSL marker, checked separately.
        result  <- if theoremDef then Right(ResolvedType.Inductive(SymbolId("<proof>"), "Proof"))
                   else resolveDeclaredType(dd.tpt.tpe, index, name, span)
      yield DefSignature(binders, result, params.map(_.symbol).zip(binders).toMap)

  private def resolveDeclaredType(
    tpe:     Type,
    index:   InductiveIndex,
    subject: String,
    span:    SourceSpan,
  ): Either[FrontendError, ResolvedType] =
    index.byClass.get(tpe.typeSymbol) match
      case Some(ind) => Right(ResolvedType.Inductive(ind.id, ind.name))
      case None      => Left(FrontendError.defError(subject,
        s"type '${tpe.show}' is not supported; verified code may only use enums " +
        "declared in the same @proofModule", span))

  private def extractDefinitions(
    body:  List[Tree],
    index: InductiveIndex,
    sigs:  Map[Symbol, DefSignature],
  ): Either[FrontendError, List[ResolvedDef]] =
    val defDefs = body.collect { case dd: DefDef if isVerifiedDef(dd.symbol) => dd }
    defDefs.foldLeft[Either[FrontendError, List[ResolvedDef]]](Right(Nil)) { (acc, dd) =>
      val sig  = sigs(dd.symbol)
      val name = dd.symbol.name.toString
      for
        done <- acc
        rhs  <- extractExpr(dd.rhs, sig.binderScope, index, sigs, name)
      yield done :+ ResolvedDef(idOf(dd.symbol), name, sig.params, sig.result, rhs, spanOf(dd))
    }

  // ================================================================
  // Verified expressions
  // ================================================================

  private def extractExpr(
    tree:    Tree,
    binders: Map[Symbol, ResolvedBinder],
    index:   InductiveIndex,
    sigs:    Map[Symbol, DefSignature],
    subject: String,
  ): Either[FrontendError, ResolvedExpr] =
    val span = spanOf(tree)
    strip(tree) match
      case t @ (_: Ident | _: Select) if binders.contains(t.symbol) =>
        Right(ResolvedExpr.Local(idOf(t.symbol), t.symbol.name.toString, span))

      case t @ (_: Ident | _: Select) if index.byCtor.contains(t.symbol) =>
        val (ind, ctor) = index.byCtor(t.symbol)
        if ctor.fields.isEmpty then Right(ResolvedExpr.Construct(ind.id, ctor.id, ctor.name, Nil, span))
        else Left(FrontendError.defError(subject,
          s"constructor '${ctor.name}' is used without its ${ctor.fields.length} argument(s)", span))

      case Apply(Select(New(tpt), _), args) if index.byCtor.contains(tpt.tpe.typeSymbol) =>
        val (ind, ctor) = index.byCtor(tpt.tpe.typeSymbol)
        constructorCall(ind, ctor, args, binders, index, sigs, subject, span)

      case app: Apply =>
        // Curried calls arrive as nested Applies; flatten them so `f(a)(b)` and
        // `f(a, b)` reach the same arity check.
        val (callee, args) = flattenApply(app)
        val sym = stripTypeApply(callee).symbol
        if index.byCtor.contains(sym) then
          val (ind, ctor) = index.byCtor(sym)
          constructorCall(ind, ctor, args, binders, index, sigs, subject, span)
        else if sigs.contains(sym) && !isTheorem(sym) then
          val sig = sigs(sym)
          if sig.params.length != args.length then
            Left(FrontendError.defError(subject,
              s"call to '${sym.name}' expects ${sig.params.length} argument(s) but got ${args.length}; " +
              "partial application is not supported in verified code", span))
          else
            extractArgs(args, binders, index, sigs, subject)
              .map(as => ResolvedExpr.Call(idOf(sym), sym.name.toString, as, span))
        else if dsl.dslTermSymbols.contains(sym) then
          Left(FrontendError.defError(subject,
            s"the proof DSL operation '${sym.name}' cannot appear in verified computation", span))
        else
          Left(FrontendError.defError(subject,
            s"calls out of the proof module are not verified code: '${sym.showFullName}'", span))

      case Match(scrutinee, cases) =>
        for
          ind      <- inductiveOfScrutinee(scrutinee, index, subject, span)
          scrut    <- extractExpr(scrutinee, binders, index, sigs, subject)
          resolved <- cases.foldLeft[Either[FrontendError, List[ResolvedCase]]](Right(Nil)) { (acc, cd) =>
                        for
                          done <- acc
                          c    <- extractCase(cd, binders, index, sigs, subject)
                        yield done :+ c
                      }
          _        <- checkBranchCoverage(ind, resolved.map(_.ctor), resolved.map(_.ctorName), subject, span)
        yield ResolvedExpr.Match(scrut, CoreTranslator.normaliseCaseOrder(ind, resolved), span)

      case Block((vd: ValDef) :: restStats, result) if isImmutableVal(vd) =>
        // Peel one binding at a time; the remaining statements stay a Block, so a
        // run of `val`s nests into nested `Let`s.  Any non-`val` statement lands
        // in the recursive call and is rejected there.
        for
          tpe   <- resolveDeclaredType(vd.tpt.tpe, index, subject, spanOf(vd))
          value <- extractExpr(vd.rhs, binders, index, sigs, subject)
          binder = ResolvedBinder(idOf(vd.symbol), vd.name.toString, tpe)
          rest   = if restStats.isEmpty then result else Block(restStats, result)
          body  <- extractExpr(rest, binders + (vd.symbol -> binder), index, sigs, subject)
        yield ResolvedExpr.Let(binder, value, body, span)

      case other =>
        Left(FrontendError.defError(subject, describeUnsupported(other), span))

  private def isImmutableVal(vd: ValDef): Boolean =
    !vd.symbol.is(Flags.Mutable) && !vd.symbol.is(Flags.Lazy) && !vd.rhs.isEmpty

  /** Peel every `Apply` layer, returning the callee and all arguments in order. */
  private def flattenApply(tree: Tree): (Tree, List[Tree]) =
    strip(tree) match
      case Apply(fn, args) =>
        val (callee, earlier) = flattenApply(fn)
        (callee, earlier ++ args)
      case other => (other, Nil)

  private def constructorCall(
    ind:     ResolvedInductive,
    ctor:    ResolvedConstructor,
    args:    List[Tree],
    binders: Map[Symbol, ResolvedBinder],
    index:   InductiveIndex,
    sigs:    Map[Symbol, DefSignature],
    subject: String,
    span:    SourceSpan,
  ): Either[FrontendError, ResolvedExpr] =
    if ctor.fields.length != args.length then
      Left(FrontendError.defError(subject,
        s"constructor '${ctor.name}' expects ${ctor.fields.length} field(s) but got ${args.length}", span))
    else
      extractArgs(args, binders, index, sigs, subject)
        .map(as => ResolvedExpr.Construct(ind.id, ctor.id, ctor.name, as, span))

  private def extractArgs(
    args:    List[Tree],
    binders: Map[Symbol, ResolvedBinder],
    index:   InductiveIndex,
    sigs:    Map[Symbol, DefSignature],
    subject: String,
  ): Either[FrontendError, List[ResolvedExpr]] =
    args.foldLeft[Either[FrontendError, List[ResolvedExpr]]](Right(Nil)) { (acc, a) =>
      for
        done <- acc
        e    <- extractExpr(a, binders, index, sigs, subject)
      yield done :+ e
    }

  private def inductiveOfScrutinee(
    scrutinee: Tree,
    index:     InductiveIndex,
    subject:   String,
    span:      SourceSpan,
  ): Either[FrontendError, ResolvedInductive] =
    index.byClass.get(scrutinee.tpe.widen.typeSymbol) match
      case Some(ind) => Right(ind)
      case None      => Left(FrontendError.defError(subject,
        s"match on '${scrutinee.tpe.widen.show}' is not supported; " +
        "only enums declared in this @proofModule can be matched", span))

  /** One branch per constructor, no duplicates.
   *
   *  Scala's exhaustivity check is not enough on its own: the branches must also
   *  line up with `IndDef.ctors`, which is why coverage is checked here and the
   *  order is normalised afterwards.
   */
  private def checkBranchCoverage(
    ind:       ResolvedInductive,
    covered:   List[SymbolId],
    coveredBy: List[String],
    subject:   String,
    span:      SourceSpan,
  ): Either[FrontendError, Unit] =
    val missing = ind.ctors.filterNot(c => covered.contains(c.id)).map(_.name)
    val dups    = coveredBy.groupBy(identity).filter(_._2.length > 1).keys.toList.sorted
    if missing.nonEmpty then
      Left(FrontendError.defError(subject,
        s"match on ${ind.name} is missing branch(es) for: ${missing.mkString(", ")}", span))
    else if dups.nonEmpty then
      Left(FrontendError.defError(subject,
        s"match on ${ind.name} has duplicate branch(es) for: ${dups.mkString(", ")}", span))
    else Right(())

  private def extractCase(
    cd:      CaseDef,
    binders: Map[Symbol, ResolvedBinder],
    index:   InductiveIndex,
    sigs:    Map[Symbol, DefSignature],
    subject: String,
  ): Either[FrontendError, ResolvedCase] =
    for
      _   <- if cd.guard.isEmpty then Right(())
             else Left(FrontendError.defError(subject,
               "pattern guards are not supported in verified code", spanOf(cd.guard)))
      pat <- extractPattern(cd.pat, index, subject)
      (_, ctor, fieldBinders, symbolScope) = pat
      body <- extractExpr(cd.body, binders ++ symbolScope, index, sigs, subject)
    yield ResolvedCase(ctor.id, ctor.name, fieldBinders, body, spanOf(cd))

  /** A pattern's constructor, its field binders in field order, and the mapping
   *  from bound symbols to those binders.
   */
  private def extractPattern(
    pat:     Tree,
    index:   InductiveIndex,
    subject: String,
  ): Either[FrontendError,
            (ResolvedInductive, ResolvedConstructor, List[ResolvedBinder], Map[Symbol, ResolvedBinder])] =
    val span = spanOf(pat)
    strip(pat) match
      case p @ (_: Ident | _: Select) if index.byCtor.contains(p.symbol) =>
        val (ind, ctor) = index.byCtor(p.symbol)
        if ctor.fields.isEmpty then Right((ind, ctor, Nil, Map.empty))
        else Left(FrontendError.defError(subject,
          s"pattern '${ctor.name}' must bind its ${ctor.fields.length} field(s)", span))

      case UnApply(fn, _, pats) if index.byCtor.contains(stripTypeApply(fn).symbol) =>
        val (ind, ctor) = index.byCtor(stripTypeApply(fn).symbol)
        if pats.length != ctor.fields.length then
          Left(FrontendError.defError(subject,
            s"pattern '${ctor.name}' binds ${pats.length} field(s) but the constructor has " +
            s"${ctor.fields.length}", span))
        else
          pats.zip(ctor.fields)
            .foldLeft[Either[FrontendError, (List[ResolvedBinder], Map[Symbol, ResolvedBinder])]](
              Right((Nil, Map.empty))
            ) { case (acc, (p, field)) =>
              for
                state <- acc
                (bs, scope) = state
                bound <- fieldBinder(p, field, subject)
              yield
                val (symOpt, binder) = bound
                (bs :+ binder, symOpt.fold(scope)(s => scope + (s -> binder)))
            }.map { case (bs, scope) => (ind, ctor, bs, scope) }

      case _: Bind =>
        Left(FrontendError.defError(subject,
          "binding the whole scrutinee (`x @ pattern`) is not supported", span))

      case _: Alternative =>
        Left(FrontendError.defError(subject,
          "pattern alternatives (`a | b`) are not supported in verified code", span))

      case _ =>
        Left(FrontendError.defError(subject,
          "unsupported pattern; only `Ctor` and `Ctor(binder, ...)` over enums of this module are allowed",
          span))

  private def fieldBinder(
    pat:     Tree,
    field:   ResolvedBinder,
    subject: String,
  ): Either[FrontendError, (Option[Symbol], ResolvedBinder)] =
    val span = spanOf(pat)
    strip(pat) match
      case b: Bind =>
        if b.name.toString == ProofRunner.IhBinderName then
          Left(FrontendError.defError(subject,
            s"a pattern binder may not be named '${ProofRunner.IhBinderName}': that name is " +
            "reserved for the generated induction hypothesis", span))
        else
          Right((Some(b.symbol), field.copy(id = idOf(b.symbol), name = b.name.toString)))
      case i: Ident if i.name == nme.WILDCARD =>
        // An unnamed field still occupies a De Bruijn slot.  It gets an id keyed
        // on source position so it stays deterministic and unreferenceable.
        Right((None, field.copy(id = SymbolId(s"<wildcard@${span.start}:${span.end}>"), name = "_")))
      case _ =>
        Left(FrontendError.defError(subject,
          "nested patterns are not supported; bind each constructor field to a name", span))

  private def describeUnsupported(tree: Tree): String = tree match
    case _: Assign   => "contains an assignment; verified definitions must be pure"
    case _: Try      => "contains a try/catch; exceptions are not supported in verified code"
    case _: Return   => "contains a return; a verified definition must be a single expression"
    case _: Closure  => "contains a function value; higher-order values are not supported"
    case _: New      => "contains a `new`; only enum constructors of this module may be constructed"
    case _: Literal  => "contains a literal; numeric and string primitives are not modelled yet"
    case _: This     => "refers to `this`; verified code may not reach outside the proof module"
    case TypeApply(fn, _) if fn.symbol.exists && fn.symbol.name == nme.asInstanceOf_ =>
      "contains a cast; verified code may not use asInstanceOf"
    case _: TypeApply => "contains a polymorphic call; type arguments are not supported"
    case Block(stats, _) if stats.exists(s => s.symbol.is(Flags.Mutable)) =>
      "contains a mutable local (var); verified definitions must be pure"
    case _: Block =>
      "contains a block with statements other than immutable `val` bindings; " +
      "verified code has no way to sequence effects"
    case t @ (_: Ident | _: Select) =>
      s"refers to '${t.symbol.showFullName}', which is neither a binder nor a constructor of this proof module"
    case t => s"contains an unsupported expression (${t.getClass.getSimpleName})"

  // ================================================================
  // Theorems and proof scripts
  // ================================================================

  private def extractTheorems(
    body:  List[Tree],
    index: InductiveIndex,
    sigs:  Map[Symbol, DefSignature],
  ): Either[FrontendError, List[ResolvedTheorem]] =
    val theoremDefs = body.collect { case dd: DefDef if isTheorem(dd.symbol) => dd }
    theoremDefs.foldLeft[Either[FrontendError, List[ResolvedTheorem]]](Right(Nil)) { (acc, dd) =>
      for
        done <- acc
        th   <- extractTheorem(dd, index, sigs)
      yield done :+ th
    }

  private def extractTheorem(
    dd:    DefDef,
    index: InductiveIndex,
    sigs:  Map[Symbol, DefSignature],
  ): Either[FrontendError, ResolvedTheorem] =
    val name = dd.symbol.name.toString
    val span = spanOf(dd)
    val sig  = sigs(dd.symbol)

    if dd.tpt.tpe.typeSymbol != dsl.proofType then
      Left(FrontendError.theoremError(name,
        s"must return exactly sroof.lang.Proof, but returns '${dd.tpt.tpe.show}'", spanOf(dd.tpt)))
    else
      strip(dd.rhs) match
        case Apply(Apply(prove, List(goalTree)), List(tacticTree))
             if stripTypeApply(strip(prove)).symbol == dsl.proveMethod =>
          for
            goal   <- extractProp(goalTree, sig.binderScope, index, sigs, name)
            tactic <- extractTactic(tacticTree, sig.binderScope, index, sigs, name, None)
          yield ResolvedTheorem(
            idOf(dd.symbol), name, sig.params, goal, tactic,
            isSimp = annotationsOf(dd.symbol).contains(dsl.simpAnnot), span)
        case _ =>
          Left(FrontendError.theoremError(name, "body must be prove(goal)(tactic)", spanOf(dd.rhs)))

  private def extractProp(
    tree:    Tree,
    binders: Map[Symbol, ResolvedBinder],
    index:   InductiveIndex,
    sigs:    Map[Symbol, DefSignature],
    subject: String,
  ): Either[FrontendError, ResolvedProp] =
    val span = spanOf(tree)
    strip(tree) match
      case Apply(Apply(eq, List(lhsTree)), List(rhsTree))
           if stripTypeApply(strip(eq)).symbol == dsl.eqMethod =>
        for
          tpe <- index.byClass.get(lhsTree.tpe.widen.typeSymbol)
                   .map(i => ResolvedType.Inductive(i.id, i.name))
                   .toRight(FrontendError.theoremError(subject,
                     s"equality at '${lhsTree.tpe.widen.show}' is not supported; both sides must " +
                     "have an enum type declared in this @proofModule", span))
          lhs <- extractExpr(lhsTree, binders, index, sigs, subject)
          rhs <- extractExpr(rhsTree, binders, index, sigs, subject)
        yield ResolvedProp(tpe, lhs, rhs, span)
      case _ =>
        Left(FrontendError.theoremError(subject,
          "goal must be an equality built with sroof's `===`", span))

  /** Where in a constructor split we are, so `ih` can be validated by identity. */
  private final case class BranchContext(
    recursiveBinder:   Option[Symbol],
    ctorName:          String,
    /** False inside `cases(...)`, which generates no hypothesis. */
    withHypothesis:    Boolean,
    /** True when this constructor's last field is of the inductive's own type. */
    hasRecursiveField: Boolean,
  )

  private def extractTactic(
    tree:    Tree,
    binders: Map[Symbol, ResolvedBinder],
    index:   InductiveIndex,
    sigs:    Map[Symbol, DefSignature],
    subject: String,
    branch:  Option[BranchContext],
  ): Either[FrontendError, ResolvedTactic] =
    val span = spanOf(tree)
    strip(tree) match
      case t if t.symbol == dsl.trivialMethod =>
        Right(ResolvedTactic.Trivial(span))

      case Apply(fn, args) if stripTypeApply(strip(fn)).symbol == dsl.simplifyMethod =>
        extractLemmas(args, subject, branch, span)
          .map(ls => ResolvedTactic.Simplify(ls, span))

      case Apply(fn, args) if stripTypeApply(strip(fn)).symbol == dsl.rewriteMethod =>
        extractLemmas(args, subject, branch, span)
          .map(ls => ResolvedTactic.Rewrite(ls, span))

      case Apply(Apply(fn, List(target)), List(casesTree))
           if stripTypeApply(strip(fn)).symbol == dsl.inductionMethod =>
        extractSplit(target, casesTree, binders, index, sigs, subject, span, withHypothesis = true)

      case Apply(Apply(fn, List(target)), List(casesTree))
           if stripTypeApply(strip(fn)).symbol == dsl.casesMethod =>
        extractSplit(target, casesTree, binders, index, sigs, subject, span, withHypothesis = false)

      case Apply(fn, _) if stripTypeApply(strip(fn)).symbol == dsl.ihMethod =>
        Left(FrontendError.theoremError(subject,
          "ih(...) is a lemma, not a tactic; use simplify(ih(...))", span))

      case _ =>
        Left(FrontendError.theoremError(subject,
          "unsupported tactic; this milestone supports trivial, " +
          "induction(x) { case ... }, and simplify(...)", span))

  private def extractLemmas(
    args:    List[Tree],
    subject: String,
    branch:  Option[BranchContext],
    span:    SourceSpan,
  ): Either[FrontendError, List[ResolvedLemmaRef]] =
    // Varargs reach us as a SeqLiteral, usually inside a Typed wrapper.
    val elems: Either[FrontendError, List[Tree]] = args match
      case List(single) => strip(single) match
        case SeqLiteral(es, _) => Right(es)
        case _ => Left(FrontendError.theoremError(subject, "simplify expects a list of lemmas", span))
      case Nil => Right(Nil)
      case _   => Left(FrontendError.theoremError(subject, "simplify expects a single argument list", span))

    elems.flatMap { es =>
      es.foldLeft[Either[FrontendError, List[ResolvedLemmaRef]]](Right(Nil)) { (acc, e) =>
        for
          done <- acc
          l    <- extractLemma(e, subject, branch)
        yield done :+ l
      }
    }

  private def extractLemma(
    tree:    Tree,
    subject: String,
    branch:  Option[BranchContext],
  ): Either[FrontendError, ResolvedLemmaRef] =
    val span = spanOf(tree)
    strip(tree) match
      case Apply(fn, List(arg)) if stripTypeApply(strip(fn)).symbol == dsl.ihMethod =>
        val argSym = strip(arg).symbol
        branch match
          case None =>
            Left(FrontendError.theoremError(subject,
              "ih(...) is only valid inside an induction branch", span))
          case Some(b) if !b.withHypothesis =>
            Left(FrontendError.theoremError(subject,
              "ih(...) is not available inside cases(...), which generates no induction " +
              "hypothesis; use induction(...) instead", span))
          case Some(b) if !b.hasRecursiveField =>
            Left(FrontendError.theoremError(subject,
              s"ih(...) is not available in the base case '${b.ctorName}': its last field is not " +
              "of the type being inducted on", span))
          case Some(b) if b.recursiveBinder.isEmpty =>
            Left(FrontendError.theoremError(subject,
              s"ih(...) needs the recursive field of '${b.ctorName}' bound to a name; " +
              "replace the `_` in that position with a binder", span))
          case Some(b) if !b.recursiveBinder.contains(argSym) =>
            Left(FrontendError.theoremError(subject,
              s"ih(${argSym.name}) is only valid for the last (recursive) field of the current " +
              s"induction branch (expected ih(${b.recursiveBinder.get.name}))", span))
          case Some(_) =>
            Right(ResolvedLemmaRef.InductionHypothesis(idOf(argSym), argSym.name.toString, span))

      case t if isTheoremRef(t) =>
        val sym = referencedTheorem(t)
        Right(ResolvedLemmaRef.Theorem(idOf(sym), sym.name.toString, span))

      case _ =>
        Left(FrontendError.theoremError(subject,
          "a simplify lemma must be ih(binder) or a reference to a @theorem in this module", span))

  private def isTheoremRef(tree: Tree): Boolean =
    val sym = referencedTheorem(tree)
    sym.exists && isTheorem(sym)

  private def referencedTheorem(tree: Tree): Symbol = strip(tree) match
    case Apply(fn, _) => stripTypeApply(strip(fn)).symbol
    case t            => stripTypeApply(t).symbol

  /** Extract `induction(x) { ... }` or `cases(x) { ... }`.
   *
   *  The two differ only in whether branches may use `ih`, which is why they
   *  share everything else — including the requirement that every constructor be
   *  covered exactly once.
   */
  private def extractSplit(
    target:         Tree,
    casesTree:      Tree,
    binders:        Map[Symbol, ResolvedBinder],
    index:          InductiveIndex,
    sigs:           Map[Symbol, DefSignature],
    subject:        String,
    span:           SourceSpan,
    withHypothesis: Boolean,
  ): Either[FrontendError, ResolvedTactic] =
    val targetTree = strip(target)
    val targetSym  = targetTree.symbol
    val what       = if withHypothesis then "induction" else "cases"
    for
      _        <- binders.get(targetSym).toRight(FrontendError.theoremError(subject,
                    s"$what target '${targetSym.name}' must be a parameter of this theorem",
                    spanOf(target)))
      ind      <- index.byClass.get(targetTree.tpe.widen.typeSymbol).toRight(
                    FrontendError.theoremError(subject,
                      s"$what target '${targetSym.name}' must have an enum type declared in " +
                      "this @proofModule", spanOf(target)))
      caseDefs <- partialFunctionCases(casesTree, subject, what)
      cases    <- caseDefs.foldLeft[Either[FrontendError, List[ResolvedTacticCase]]](Right(Nil)) { (acc, cd) =>
                    for
                      done <- acc
                      c    <- extractTacticCase(cd, binders, index, sigs, subject, withHypothesis)
                    yield done :+ c
                  }
      _        <- checkBranchCoverage(ind, cases.map(_.ctor), cases.map(_.ctorName), subject, span)
    yield
      val ordered = CoreTranslator.normaliseTacticCaseOrder(ind, cases)
      val id      = idOf(targetSym)
      val name    = targetSym.name.toString
      if withHypothesis then ResolvedTactic.Induction(id, name, ordered, span)
      else ResolvedTactic.Cases(id, name, ordered, span)

  /** Pull the branches out of the `PartialFunction` literal passed to the tactic.
   *
   *  At this phase a pattern-matching anonymous function is still
   *  `Block(List(DefDef($anonfun)), Closure(...))`, whose body is a `Match` on a
   *  synthetic parameter — much closer to the source than the class it becomes
   *  later, which is one reason this phase runs before `pickler`.
   */
  private def partialFunctionCases(
    tree:    Tree,
    subject: String,
    what:    String,
  ): Either[FrontendError, List[CaseDef]] =
    def malformed(at: Tree) = Left(FrontendError.theoremError(subject,
      s"$what branches must be written as `{ case Ctor(...) => tactic }`", spanOf(at)))
    strip(tree) match
      case Block(List(dd: DefDef), _: Closure) =>
        strip(dd.rhs) match
          case Match(_, cases) => Right(cases)
          case other           => malformed(other)
      case other => malformed(other)

  private def extractTacticCase(
    cd:             CaseDef,
    binders:        Map[Symbol, ResolvedBinder],
    index:          InductiveIndex,
    sigs:           Map[Symbol, DefSignature],
    subject:        String,
    withHypothesis: Boolean,
  ): Either[FrontendError, ResolvedTacticCase] =
    for
      _   <- if cd.guard.isEmpty then Right(())
             else Left(FrontendError.theoremError(subject,
               "pattern guards are not supported in tactic branches", spanOf(cd.guard)))
      pat <- extractPattern(cd.pat, index, subject).left.map(e =>
               FrontendError.theoremError(subject, e.message, e.span))
      (_, ctor, fieldBinders, symbolScope) = pat
      hasRecursiveField = index.recursiveCtors.contains(ctor.id)
      // The hypothesis is about the *last* field, which is the one the tactic
      // engine applies the recursion to.  Look it up by binder identity rather
      // than by iterating the scope map, whose order is unspecified.
      recursiveBinder = if !hasRecursiveField then None
                        else fieldBinders.lastOption.flatMap { last =>
                          symbolScope.collectFirst { case (sym, b) if b.id == last.id => sym }
                        }
      branch  = BranchContext(recursiveBinder, ctor.name, withHypothesis, hasRecursiveField)
      tactic <- extractTactic(cd.body, binders ++ symbolScope, index, sigs, subject, Some(branch))
    yield ResolvedTacticCase(
      ctor.id, ctor.name, fieldBinders, usesIh = mentionsIh(tactic), tactic, spanOf(cd))

  private def mentionsIh(tactic: ResolvedTactic): Boolean =
    def isIh(l: ResolvedLemmaRef) = l match
      case _: ResolvedLemmaRef.InductionHypothesis => true
      case _                                       => false
    tactic match
      case ResolvedTactic.Trivial(_)             => false
      case ResolvedTactic.Simplify(ls, _)        => ls.exists(isIh)
      case ResolvedTactic.Rewrite(ls, _)         => ls.exists(isIh)
      case ResolvedTactic.Induction(_, _, cs, _) => cs.exists(c => mentionsIh(c.tactic))
      case ResolvedTactic.Cases(_, _, cs, _)     => cs.exists(c => mentionsIh(c.tactic))
