package sroof.plugin.dotc

import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Names.{Name, termName, typeName}
import dotty.tools.dotc.core.Symbols.{Symbol, requiredClass, requiredModule, requiredPackage}

/** Resolved symbols for the sroof DSL and annotations.
 *
 *  Every recognition decision in the extractor compares against one of these
 *  symbols.  Nothing is matched by spelling, so a user-defined `prove`,
 *  `trivial`, or `===` is ordinary Scala as far as sroof is concerned.
 *
 *  Resolved once per compiler run and never cached statically: the symbols
 *  belong to the run's `Context`, and holding them across runs would leak
 *  denotations between compilations.
 */
final class DslSymbols private (
  val proofModuleAnnot: Symbol,
  val theoremAnnot:     Symbol,
  val simpAnnot:        Symbol,
  val propType:         Symbol,
  val proofType:        Symbol,
  val tacticType:       Symbol,
  val eqMethod:         Symbol,
  val proveMethod:      Symbol,
  val trivialMethod:    Symbol,
  val inductionMethod:  Symbol,
  val ihMethod:         Symbol,
  val simplifyMethod:   Symbol,
):
  /** All DSL term symbols, for "did the user mean a sroof call?" diagnostics. */
  def dslTermSymbols: Set[Symbol] =
    Set(eqMethod, proveMethod, trivialMethod, inductionMethod, ihMethod, simplifyMethod)

object DslSymbols:

  /** Thrown only when the sroof API is missing from the classpath entirely.
   *  Turned into a compiler error by the phase — never a silent success.
   */
  final class MissingApi(message: String) extends Exception(message)

  /** The synthetic object holding `sroof.lang`'s top-level definitions.
   *
   *  Scala 3 wraps top-level definitions in an object named after the source
   *  file, so `sroof/lang/lang.scala` produces `sroof.lang.lang$package`.  The
   *  file name is therefore load-bearing and must not change without updating
   *  this constant.
   */
  private val LangPackageObject = "sroof.lang.lang$package"

  /** Resolve the DSL, or return `None` when the sroof API is absent entirely.
   *
   *  Absence is not an error: a compilation with no sroof API on the classpath
   *  cannot contain a `@proofModule`, so the plugin has nothing to verify and
   *  stays inert.  A *partially* present API is a different matter and throws
   *  [[MissingApi]] — that means the build is broken, and failing loudly beats
   *  quietly verifying nothing.
   */
  def resolve()(using Context): Option[DslSymbols] =
    val annotationsPresent =
      try requiredClass("sroof.annotation.proofModule").exists
      catch case _: Exception => false
    if !annotationsPresent then None else Some(apply())

  def apply()(using Context): DslSymbols =
    val langOwner =
      try requiredModule(LangPackageObject).moduleClass
      catch
        case ex: Exception =>
          throw MissingApi(
            s"could not find $LangPackageObject — is sroof-scala-api on the compilation classpath? (${ex.getMessage})")

    def member(name: Name): Symbol =
      val denot = langOwner.info.member(name)
      if !denot.exists then
        throw MissingApi(s"sroof API is missing '${name.show}' in $LangPackageObject")
      denot.suchThat(_.exists).symbol

    def annot(fqn: String): Symbol =
      try requiredClass(fqn)
      catch
        case ex: Exception =>
          throw MissingApi(s"could not find annotation $fqn (${ex.getMessage})")

    new DslSymbols(
      proofModuleAnnot = annot("sroof.annotation.proofModule"),
      theoremAnnot     = annot("sroof.annotation.theorem"),
      simpAnnot        = annot("sroof.annotation.simp"),
      propType         = member(typeName("Prop")),
      proofType        = member(typeName("Proof")),
      tacticType       = member(typeName("Tactic")),
      eqMethod         = member(termName("===")),
      proveMethod      = member(termName("prove")),
      trivialMethod    = member(termName("trivial")),
      inductionMethod  = member(termName("induction")),
      ihMethod         = member(termName("ih")),
      simplifyMethod   = member(termName("simplify")),
    )
