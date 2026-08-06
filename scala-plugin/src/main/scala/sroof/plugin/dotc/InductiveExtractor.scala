package sroof.plugin.dotc

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.NameOps.stripModuleClassSuffix
import dotty.tools.dotc.core.StdNames.nme
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.core.Types.{MethodType, Type}

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

    def fieldType(tpe: Type, at: SourceSpan): Either[FrontendError, ResolvedType] =
      val sym = tpe.typeSymbol
      if enumClasses.contains(sym) then Right(ResolvedType.Inductive(idOf(sym), sym.name.toString))
      else Left(FrontendError.enumError(name,
        s"field type '${tpe.show}' is not an enum declared in this @proofModule", at))

    if cls.typeParams.nonEmpty then
      Left(FrontendError.enumError(name, "generic enums are not supported in this milestone", span))
    else
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
            built <- buildConstructor(child, cls, name, fieldType)
          yield
            val (ctor, childAliases, isRecursive) = built
            (ctors :+ ctor,
             aliases ++ childAliases.map(_ -> ctor),
             if isRecursive then recursive + ctor.id else recursive)
        }.map { case (ctors, aliases, recursive) =>
          (ResolvedInductive(idOf(cls), name, ctors, span), aliases, recursive)
        }

  private def buildConstructor(
    child:     Symbol,
    enumClass: Symbol,
    enumName:  String,
    fieldType: (Type, SourceSpan) => Either[FrontendError, ResolvedType],
  )(using Context): Either[FrontendError, (ResolvedConstructor, List[Symbol], Boolean)] =
    val span = spanOfSym(child)
    val name = child.name.stripModuleClassSuffix.toString

    if !child.isClass then
      // A singleton case (`case Zero`): the registered child is the value itself.
      Right((ResolvedConstructor(idOf(child), name, Nil, span), List(child), false))
    else
      val cls    = child.asClass
      val module = cls.companionModule
      cls.primaryConstructor.info match
        case mt: MethodType =>
          mt.paramNames.zip(mt.paramInfos).zipWithIndex
            .foldLeft[Either[FrontendError, List[ResolvedBinder]]](Right(Nil)) {
              case (acc, ((pname, ptpe), i)) =>
                for
                  done <- acc
                  t    <- fieldType(ptpe, span)
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
              // Recursive only when the single (hence last) field is the enum
              // itself: `Builtins.buildFixCase` applies the recursion to Var(0),
              // the last constructor argument.
              val isRecursive =
                fields.length == 1 &&
                fields.head.tpe == ResolvedType.Inductive(idOf(enumClass), enumName)
              (ResolvedConstructor(idOf(cls), name, fields, span), aliases, isRecursive)
            }
        case other =>
          Left(FrontendError.enumError(enumName,
            s"case '$name' has an unsupported constructor shape (${other.show})", span))
