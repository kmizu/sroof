package sroof.it

import munit.FunSuite
import java.nio.file.{Files, Paths}
import sroof.extract.Extractor
import sroof.syntax.{Parser, Elaborator}

/** How much of the shipped corpus extracts to Scala that actually compiles.
  *
  * v0.18 fixed two defects that made *every* extraction invalid. Sweeping the
  * whole corpus afterwards showed the rest of the gap: 8 of 26 files compile.
  *
  * The 18 that do not fail for one dominant reason. `termToScalaType` renders an
  * unresolved `Var(i)` as the literal name `T0`, `T1`, … — a type that is never
  * declared:
  *
  * {{{
  *   E.scala:21: Missing type parameter for [A] =>> PList[<error Not found: type T0>]
  * }}}
  *
  * A `.sroof` definition takes its type parameter as an ordinary `Type`-valued
  * parameter — `def poly_length(A: Type, xs: PolyList(A))` — and extraction has to
  * turn that into a Scala *generic*, `def polyLength[A](xs: PList[A])`. It does not
  * yet, so every polymorphic definition, and every file containing one, is lost.
  *
  * This suite pins the two halves separately: the files that compile must keep
  * compiling, and the count that do not must not grow. Fixing the generics gap
  * will move files from the second list to the first, and the count assertion is
  * written so that doing so fails the test and forces the lists to be updated —
  * which is the point.
  */
class ExtractionCorpusSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(1200, "s")

  /** Files whose extraction compiles today. */
  private val compiling = Set(
    "examples/bool.sroof",
    "examples/nat.sroof",
    "examples/safe_division.sroof",
    "examples/verified_ordering.sroof",
    "examples/verified_stack.sroof",
    "stdlib/Bool.sroof",
    "stdlib/Nat.sroof",
    "stdlib/Pair.sroof",
  )

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

  test("every file known to extract cleanly still does"):
    val files = corpus
    assert(files.length > 20, s"expected the shipped corpus, found ${files.length}")
    val broken = compiling.toList.sorted.flatMap { path =>
      val r = CompilerHarness.compile("E.scala" -> extractOf(path))
      if r.failed then
        Some(s"$path -> ${r.report.linesIterator.filter(_.contains("error")).take(1).mkString.take(200)}")
      else None
    }
    assert(broken.isEmpty, s"these used to extract to compiling Scala:\n${broken.mkString("\n")}")

  test("the extraction gap does not grow"):
    // Not an endorsement of the gap — a measurement of it. If a fix makes more
    // files compile this fails, and the `compiling` set above must be extended.
    val failing = corpus.filterNot(compiling.contains).filter { path =>
      CompilerHarness.compile("E.scala" -> extractOf(path)).failed
    }
    assertEquals(
      failing.length,
      corpus.length - compiling.size,
      s"the set of files whose extraction does not compile changed:\n${failing.mkString("\n")}",
    )
