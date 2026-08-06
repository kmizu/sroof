package sroof.plugin.dotc

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Flags
import dotty.tools.dotc.core.Names.TermName
import dotty.tools.dotc.core.Symbols.Symbol
import dotty.tools.dotc.util.SourcePosition

import sroof.frontend.{SourceSpan, SymbolId}

/** Small dotc helpers shared by the extraction layer.
 *
 *  Kept together so that the rules they encode — what counts as a transparent
 *  wrapper, what a canonical symbol identity is, where an annotation may live —
 *  have exactly one definition each.
 */
object ExtractorSupport:
  import tpd.*

  // ---- positions ----

  def spanOf(tree: Tree)(using Context): SourceSpan = fromPos(tree.sourcePos)

  def spanOfSym(sym: Symbol)(using Context): SourceSpan =
    if sym.span.exists then fromPos(sym.sourcePos) else SourceSpan.synthetic

  private def fromPos(pos: SourcePosition): SourceSpan =
    if !pos.exists then SourceSpan.synthetic
    else SourceSpan(pos.source.file.path, pos.span.start, pos.span.end, pos.line + 1, pos.column + 1)

  // ---- identity ----

  /** A canonical identity for a symbol.
   *
   *  The fully qualified name alone is ambiguous for overloads and for distinct
   *  locals sharing a name, so the symbol's unique id is appended.  Ids are
   *  stable within one compiler run, the only scope they are compared in.
   */
  def idOf(sym: Symbol)(using Context): SymbolId = SymbolId(s"${sym.fullName}#${sym.id}")

  def memberOpt(owner: Symbol, name: TermName)(using Context): Option[Symbol] =
    if !owner.exists then None
    else
      val denot = owner.info.member(name)
      if denot.exists then Some(denot.suchThat(_.exists).symbol) else None

  // ---- annotations ----

  /** Annotations on a declaration.  For an `object`, dotc may attach them to the
   *  module value rather than to its class, so both are consulted.
   */
  def annotationsOf(sym: Symbol)(using Context): List[Symbol] =
    val own = sym.annotations.map(_.symbol)
    val fromModule =
      if sym.is(Flags.ModuleClass) && sym.sourceModule.exists
      then sym.sourceModule.annotations.map(_.symbol) else Nil
    own ++ fromModule

  // ---- tree normalisation ----

  /** Strip wrappers the typer leaves behind that carry no semantics.
   *
   *  A non-empty `Inlined` binding list is not transparent, so it is left in
   *  place to be rejected rather than silently discarded.
   */
  def strip(tree: Tree): Tree = tree match
    case Typed(expr, _)        => strip(expr)
    case Inlined(_, Nil, expr) => strip(expr)
    case Block(Nil, expr)      => strip(expr)
    case Annotated(expr, _)    => strip(expr)
    case _                     => tree

  def stripTypeApply(tree: Tree): Tree = tree match
    case TypeApply(fn, _) => stripTypeApply(fn)
    case _                => tree
