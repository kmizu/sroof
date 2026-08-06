package sroof.plugin.dotc

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.NameOps.stripModuleClassSuffix
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.Types.{MethodType, PolyType, Type}

import sroof.frontend.*

/** The enums of one proof module, indexed for identity lookup.
 *
 *  `byCtor` maps every symbol that can *denote* a constructor — the case class or
 *  enum value, its constructor, and its companion's `apply`/`unapply` — onto that
 *  constructor.  One map therefore serves both expressions and patterns.
 */
final case class InductiveIndex(
  all:     List[ResolvedInductive],
  byClass: Map[Symbol, ResolvedInductive],
  byCtor:  Map[Symbol, (ResolvedInductive, ResolvedConstructor)],
  /** Constructors with exactly one field of their own inductive type — the only
   *  shape for which an induction hypothesis can be generated. */
  recursiveCtors: Set[SymbolId],
):
  def indOf(ctorId: SymbolId): Option[ResolvedInductive] =
    all.find(_.ctors.exists(_.id == ctorId))

object InductiveIndex:
  val empty: InductiveIndex = InductiveIndex(Nil, Map.empty, Map.empty, Set.empty)

/** Translates the `enum` declarations of a proof module into IR inductives. */
object InductiveExtractor:
  import tpd.*
  import ExtractorSupport.*

  def extract(body: List[Tree])(using Context): Either[FrontendError, InductiveIndex] =
    val enumDefs = body.collect {
      case td: TypeDef if td.symbol.isClass && td.symbol.is(Flags.Enum) && !td.symbol.is(Flags.Case) => td
    }
    val enumClasses = enumDefs.map(_.symbol).toSet

    enumDefs.foldLeft[Either[FrontendError, InductiveIndex]](Right(InductiveIndex.empty)) { (acc, td) =>
      for
        index <- acc
        built <- buildInductive(td, enumClasses)
      yield
        val (ind, aliases, recursive) = built
        InductiveIndex(
          index.all :+ ind,
          index.byClass + (td.symbol -> ind),
          index.byCtor ++ aliases.map((s, c) => s -> (ind, c)),
          index.recursiveCtors ++ recursive,
        )
    }

  private def buildInductive(
    td:          TypeDef,
    enumClasses: Set[Symbol],
  )(using Context): Either[FrontendError, (ResolvedInductive, List[(Symbol, ResolvedConstructor)], Set[SymbolId])] =
    val cls  = td.symbol
    val name = cls.name.toString
    val span = spanOf(td)

    val typeParams = cls.typeParams.map(tp =>
      ResolvedBinder(idOf(tp), tp.name.toString, ResolvedType.TypeVar(idOf(tp), tp.name.toString)))
    val typeParamIds: Map[Symbol, SymbolId] =
      cls.typeParams.map(tp => (tp: Symbol) -> idOf(tp)).toMap

    // `own` maps a *constructor's* own type parameters onto the enum's, by
    // position: dotc gives `case Cons[A](...)` its own `A`, distinct from the
    // `A` of `enum Lst[A]`, and a field's type mentions the former.
    def fieldType(
      tpe: Type,
      at:  SourceSpan,
      own: Map[Symbol, SymbolId],
    ): Either[FrontendError, ResolvedType] =
      val sym = tpe.typeSymbol
      if own.contains(sym) then
        Right(ResolvedType.TypeVar(own(sym), sym.name.toString))
      else if typeParamIds.contains(sym) then
        Right(ResolvedType.TypeVar(typeParamIds(sym), sym.name.toString))
      else if enumClasses.contains(sym) then
        // A field of an enum type carries that enum's own type arguments.
        tpe.argInfos.foldLeft[Either[FrontendError, List[ResolvedType]]](Right(Nil)) { (acc, a) =>
          for
            done <- acc
            t    <- fieldType(a, at, own)
          yield done :+ t
        }.map(args => ResolvedType.Inductive(idOf(sym), sym.name.toString, args))
      else Left(FrontendError.enumError(name,
        s"field type '${tpe.show}' is not an enum or type parameter of this @proofModule", at))

    locally:
      // `children` are the enum's cases.  Sorting by source offset pins the order
      // to what the user wrote, which is exactly what `IndDef.ctors` order means.
      val children = cls.children.sortBy(_.span.start)
      if children.isEmpty then Left(FrontendError.enumError(name, "has no cases", span))
      else
        children.foldLeft[Either[FrontendError,
          (List[ResolvedConstructor], List[(Symbol, ResolvedConstructor)], Set[SymbolId])]](
          Right((Nil, Nil, Set.empty))
        ) { (acc, child) =>
          for
            state <- acc
            (ctors, aliases, recursive) = state
            built <- buildConstructor(child, cls, name, typeParams.map(_.id), fieldType)
          yield
            val (ctor, childAliases, isRecursive) = built
            (ctors :+ ctor,
             aliases ++ childAliases.map(_ -> ctor),
             if isRecursive then recursive + ctor.id else recursive)
        }.map { case (ctors, aliases, recursive) =>
          (ResolvedInductive(idOf(cls), name, ctors, span, typeParams), aliases, recursive)
        }

  private def buildConstructor(
    child:       Symbol,
    enumClass:   Symbol,
    enumName:    String,
    enumParamIds: List[SymbolId],
    fieldType:   (Type, SourceSpan, Map[Symbol, SymbolId]) => Either[FrontendError, ResolvedType],
  )(using Context): Either[FrontendError, (ResolvedConstructor, List[Symbol], Boolean)] =
    val span = spanOfSym(child)
    val name = child.name.stripModuleClassSuffix.toString

    if !child.isClass then
      // A singleton case (`case Zero`): the registered child is the value itself.
      Right((ResolvedConstructor(idOf(child), name, Nil, span), List(child), false))
    else
      val cls    = child.asClass
      val module = cls.companionModule
      // A generic case class has a `PolyType` constructor wrapping the value
      // parameters.  Peeling it naively leaves the field types referring to the
      // PolyType's own binders, which have no symbol to look up — so instantiate
      // it at the *enum's* type parameters first.  That also makes each case's
      // parameters line up with the enum's positionally, which is what the IR
      // and the core `IndDef` both assume.
      def valueParams(t: Type): Option[MethodType] = t match
        case pt: PolyType   => valueParams(pt.instantiate(enumClass.typeParams.map(_.typeRef)))
        case mt: MethodType => Some(mt)
        case _              => None

      val ownParams: Map[Symbol, SymbolId] =
        cls.typeParams.zip(enumParamIds).map { case (tp, id) => (tp: Symbol) -> id }.toMap

      valueParams(cls.primaryConstructor.info) match
        case Some(mt) =>
          mt.paramNames.zip(mt.paramInfos).zipWithIndex
            .foldLeft[Either[FrontendError, List[ResolvedBinder]]](Right(Nil)) {
              case (acc, ((pname, ptpe), i)) =>
                for
                  done <- acc
                  t    <- fieldType(ptpe, span, ownParams)
                yield done :+ ResolvedBinder(
                  SymbolId(s"${cls.fullName}#${cls.id}.field$i"), pname.toString, t)
            }
            .map { fields =>
              val companionAliases =
                if module.exists then
                  List(module, module.moduleClass) ++
                  List(memberOpt(module.moduleClass, nme.apply),
                       memberOpt(module.moduleClass, nme.unapply)).flatten
                else Nil
              val aliases = List(cls, cls.primaryConstructor) ++ companionAliases
              // A hypothesis can be generated exactly when the **last** field is
              // the enum itself: `Builtins.buildFixCase` applies the recursion to
              // Var(0), which is the last constructor argument.  Earlier fields
              // may be anything, including other recursive occurrences — but an
              // `ih` about one of those is rejected during tactic extraction,
              // since the engine can only build the hypothesis for Var(0).
              val isRecursive = fields.lastOption.exists {
                _.tpe match
                  case ResolvedType.Inductive(id, _, _) => id == idOf(enumClass)
                  case _                                => false
              }
              (ResolvedConstructor(idOf(cls), name, fields, span), aliases, isRecursive)
            }
        case None =>
          Left(FrontendError.enumError(enumName,
            s"case '$name' has an unsupported constructor shape " +
            s"(${cls.primaryConstructor.info.show})", span))
