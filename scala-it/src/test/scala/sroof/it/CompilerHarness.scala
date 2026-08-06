package sroof.it

import java.nio.file.{Files, Path}

import dotty.tools.dotc.Main
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.reporting.{Diagnostic, Reporter}

import scala.collection.mutable.ListBuffer
import scala.jdk.CollectionConverters.*

/** Runs a genuine Scala 3 compilation with the sroof plugin enabled.
 *
 *  Nothing here fakes the compiler: sources go through the real `dotc` pipeline,
 *  the plugin is loaded from the packaged JAR via `-Xplugin`, and the result is
 *  whatever the compiler concluded.  Unit-testing hand-built IR would not tell
 *  us whether the plugin is loaded, correctly scheduled, or extracting the right
 *  trees; this does.
 */
object CompilerHarness:

  final case class Result(errors: List[String], warnings: List[String]):
    def succeeded: Boolean = errors.isEmpty
    def failed: Boolean    = errors.nonEmpty

    /** Errors the sroof plugin produced, as opposed to ordinary Scala errors. */
    def sroofErrors: List[String] = errors.filter(_.contains("[sroof]"))

    def hasSroofError: Boolean = sroofErrors.nonEmpty

    def mentions(fragment: String): Boolean = errors.exists(_.contains(fragment))

    def report: String =
      if errors.isEmpty then "<compilation succeeded>" else errors.mkString("\n")

  private lazy val config: Map[String, String] =
    val stream = getClass.getClassLoader.getResourceAsStream("sroof-it.properties")
    if stream == null then
      sys.error("sroof-it.properties is missing; the sbt resource generator did not run")
    try
      scala.io.Source.fromInputStream(stream).getLines()
        .filter(_.contains("="))
        .map { line =>
          val i = line.indexOf('=')
          line.substring(0, i) -> line.substring(i + 1)
        }.toMap
    finally stream.close()

  private def pluginClasspath: String  = config("pluginClasspath")
  private def compileClasspath: String = config("compileClasspath")

  private class Collecting extends Reporter:
    val diagnostics: ListBuffer[Diagnostic] = ListBuffer.empty
    def doReport(dia: Diagnostic)(using Context): Unit = diagnostics += dia

  /** Compile the given sources; `sources` maps a file name to its content. */
  def compile(sources: (String, String)*): Result =
    val dir = Files.createTempDirectory("sroof-it")
    val out = Files.createDirectory(dir.resolve("classes"))
    try
      val files = sources.map { (name, content) =>
        val f = dir.resolve(name)
        Files.writeString(f, content)
        f.toAbsolutePath.toString
      }
      val reporter = Collecting()
      val args = Array(
        "-classpath", compileClasspath,
        "-d", out.toAbsolutePath.toString,
        "-usejavacp:false",
        s"-Xplugin:$pluginClasspath",
      ) ++ files
      Main.process(args, reporter)
      val messages = reporter.diagnostics.toList
      // Severity constants live on the compiler's public `interfaces.Diagnostic`.
      import dotty.tools.dotc.interfaces.Diagnostic as IDiagnostic
      Result(
        errors   = messages.filter(_.level >= IDiagnostic.ERROR).map(render),
        warnings = messages.filter(_.level == IDiagnostic.WARNING).map(render),
      )
    finally deleteRecursively(dir)

  /** Compile a proof module wrapped in the standard preamble. */
  def compileModule(body: String, fileName: String = "Fixture.scala"): Result =
    compile(fileName ->
      s"""package fixture
         |
         |import sroof.annotation.*
         |import sroof.lang.*
         |
         |$body
         |""".stripMargin)

  private def render(dia: Diagnostic): String =
    val pos = if dia.pos.exists then s"${dia.pos.source.name}:${dia.pos.line + 1}: " else ""
    s"$pos${dia.message}"

  private def deleteRecursively(path: Path): Unit =
    if Files.exists(path) then
      Files.walk(path).iterator().asScala.toList.reverse.foreach(Files.deleteIfExists)
