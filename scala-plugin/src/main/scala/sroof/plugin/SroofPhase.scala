package sroof.plugin

import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.core.Contexts.{Context, ctx}
import dotty.tools.dotc.plugins.PluginPhase
import dotty.tools.dotc.report
import dotty.tools.dotc.transform.{Pickler, PostTyper}
import dotty.tools.dotc.util.{SourcePosition, Spans}

import scala.util.control.NonFatal

import sroof.frontend.{FrontendError, ModuleVerifier, SourceSpan}
import sroof.plugin.dotc.{DslSymbols, TreeExtractor}

/** The sroof verification phase.
 *
 *  ## Phase placement
 *
 *  Scheduled after `posttyper` and before `pickler`, using the compiler's own
 *  phase-name constants rather than string literals so a rename cannot silently
 *  detach the phase.  In Scala 3.3.6 the order is
 *  `typer → posttyper → … → pickler → inlining → …`, which gives this phase what
 *  it needs and nothing it does not:
 *
 *  - every reference has a resolved symbol and every expression a type;
 *  - source positions are still the user's, so diagnostics point at real code;
 *  - enum cases, method bodies, applications, and matches are still recognisable
 *    — in particular a `PartialFunction` literal is still a closure over a
 *    `Match`, not the anonymous class it becomes later;
 *  - it runs before TASTy is written, so a rejected proof fails the compilation
 *    rather than being pickled first.
 *
 *  ## State
 *
 *  The phase holds no mutable state and no static state: symbols are resolved
 *  from the run's `Context` on each module, so nothing leaks between compiler
 *  runs sharing a JVM.
 */
class SroofPhase extends PluginPhase:
  import tpd.*

  val phaseName: String = SroofPhase.name

  override val runsAfter:  Set[String] = Set(PostTyper.name)
  override val runsBefore: Set[String] = Set(Pickler.name)

  /** DSL symbols for the current run.
   *
   *  Scoped to one compiler run and recomputed when the run changes, so symbols
   *  from a finished compilation are never consulted by a later one sharing the
   *  JVM.  This is the phase's only mutable state.
   */
  private var cachedRun: AnyRef | Null = null
  private var cachedDsl: Option[DslSymbols] = None

  private def dslSymbols(using Context): Option[DslSymbols] =
    val run = ctx.run
    if !cachedRun.eq(run) then
      cachedRun = run
      cachedDsl = DslSymbols.resolve()
    cachedDsl

  override def transformTypeDef(tree: TypeDef)(using Context): Tree =
    if tree.symbol.isClass then
      guarded(s"verifying ${tree.name}", tree) { extractor =>
        if extractor.isProofModule(tree.symbol) then verify(tree, extractor)
      }
    tree

  /** Catch `@theorem` methods written outside a `@proofModule`.
   *
   *  Without this the annotation would simply be ignored, and an unproved
   *  "theorem" would compile clean — the worst possible failure mode.
   */
  override def transformDefDef(tree: DefDef)(using Context): Tree =
    guarded(s"checking ${tree.name}", tree) { extractor =>
      if extractor.isTheorem(tree.symbol) && !extractor.isProofModule(tree.symbol.owner) then
        error(
          s"theorem ${tree.name}: @theorem is only verified inside a @proofModule object; " +
          "this method would compile without being proved",
          tree.sourcePos)
    }
    tree

  /** Run plugin logic with the DSL resolved, turning any internal failure into a
   *  compiler error.  An exception must never leave the compilation looking clean.
   */
  private def guarded(what: String, at: Tree)(body: TreeExtractor => Unit)(using Context): Unit =
    try dslSymbols.foreach(dsl => body(TreeExtractor(dsl)))
    catch
      case ex: DslSymbols.MissingApi =>
        error(ex.getMessage, at.sourcePos)
      case NonFatal(ex) =>
        error(s"internal error while $what: ${ex.getClass.getName}: ${ex.getMessage}", at.sourcePos)

  private def verify(tree: TypeDef, extractor: TreeExtractor)(using Context): Unit =
    extractor.extractModule(tree).flatMap(ModuleVerifier.verify) match
      case Right(_)  => ()
      case Left(err) => error(err.render, positionOf(err, tree))

  /** Turn a frontend span back into a compiler position.
   *
   *  Spans are recorded against the unit being compiled, so the offsets are
   *  valid in `ctx.source`.  A synthetic span falls back to the module's own
   *  position rather than reporting at an arbitrary offset.
   */
  private def positionOf(err: FrontendError, fallback: Tree)(using Context): SourcePosition =
    val span = err.span
    if span == SourceSpan.synthetic || span.end < span.start then fallback.sourcePos
    else if span.end > ctx.source.content().length then fallback.sourcePos
    else SourcePosition(ctx.source, Spans.Span(span.start, span.end))

  private def error(message: String, pos: SourcePosition)(using Context): Unit =
    report.error(s"[sroof] $message", pos)

object SroofPhase:
  val name: String = "sroofVerify"
