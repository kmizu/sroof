package sroof.it

import munit.FunSuite
import java.nio.file.{Files, Paths}
import sroof.extract.Extractor
import sroof.syntax.{Parser, Elaborator}

/** Every shipped `.sroof` file extracts to Scala that compiles.
  *
  * This suite arrived in v0.19 as a measurement rather than a guarantee: 8 of 26
  * files compiled, and it pinned the failing count so that a fix would have to come
  * back and update it. v0.20 is that fix — all 26 compile, and the exception list is
  * empty.
  *
  * Compiling is not the same as being right, which is what `ExtractionRuntimeSuite`
  * is for. This one is the breadth check: it is the only test that runs the whole
  * corpus through the extractor, and the failures it caught were spread across five
  * independent defects that no single example would have shown.
  */
class ExtractionCorpusSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(1200, "s")

  /** Files whose extraction is known not to compile.
    *
    * Empty, and meant to stay that way. An entry here is a documented hole, not a
    * pass: adding one means saying in the comment what cannot be extracted and why.
    */
  private val exceptions = Set.empty[String]

  private def corpus: List[String] =
    (Option(Paths.get("stdlib").toFile.listFiles).toList.flatten ++
     Option(Paths.get("examples").toFile.listFiles).toList.flatten)
      .filter(_.getName.endsWith(".sroof")).map(_.getPath).sorted

  private def extractOf(path: String): String =
    val src = Files.readString(Paths.get(path))
    val out = for
      d <- Parser.parseProgram(src).left.map(_.toString)
      r <- Elaborator.elaborate(d).left.map(_.message)
    yield Extractor.extractProgram(r.env)
    out.fold(e => fail(s"$path: extraction failed outright: $e"), identity)

  test("every shipped .sroof file extracts to compiling Scala"):
    val files = corpus
    assert(files.length > 20, s"expected the shipped corpus, found ${files.length}")
    val broken = files.filterNot(exceptions.contains).flatMap { path =>
      val r = CompilerHarness.compile("E.scala" -> extractOf(path))
      if r.failed then
        Some(s"$path -> ${r.report.linesIterator.filter(_.contains("error")).take(1).mkString.take(200)}")
      else None
    }
    assert(broken.isEmpty, s"${broken.length} of ${files.length} do not compile:\n${broken.mkString("\n")}")

  test("the exception list names only files that are really in the corpus"):
    // A stale entry would silently excuse a file that no longer exists, and quietly
    // shrink what the test above covers.
    val missing = exceptions -- corpus.toSet
    assert(missing.isEmpty, s"exceptions name files not in the corpus: $missing")
