package sroof

import java.nio.file.{Files, Paths}
import scala.jdk.CollectionConverters.*
import munit.FunSuite

class LemmaBundleSuite extends FunSuite:

  private val bundleDir = Paths.get("stdlib/bundles")

  private def read(path: java.nio.file.Path): String =
    Files.readString(path)

  private def bundleEntries(path: java.nio.file.Path): List[String] =
    read(path).linesIterator
      .map(_.trim)
      .filter(line => line.nonEmpty && !line.startsWith("#"))
      .toList

  test("at least three practical bundles are available"):
    assert(Files.isDirectory(bundleDir), "stdlib/bundles must exist")
    val bundles = Files.list(bundleDir).iterator().asScala.toList.filter(_.toString.endsWith(".bundle"))
    assert(bundles.length >= 3, s"expected >= 3 bundles, got ${bundles.map(_.getFileName)}")
    bundles.foreach { b =>
      val entries = bundleEntries(b)
      assert(entries.nonEmpty, s"bundle must contain at least one lemma: ${b.getFileName}")
    }

  test("bundle entries reference known stdlib lemma names"):
    val stdlibText =
      List("examples/nat.sroof", "examples/list.sroof", "examples/bool.sroof")
        .map(path => read(Paths.get(path)))
        .mkString("\n")

    val bundles = Files.list(bundleDir).iterator().asScala.toList.filter(_.toString.endsWith(".bundle"))
    bundles.foreach { b =>
      bundleEntries(b).foreach { lemma =>
        assert(
          stdlibText.contains(s"defspec $lemma"),
          s"bundle lemma '$lemma' must exist in stdlib defspecs (${b.getFileName})",
        )
      }
    }

  test("bundle compatibility policy is documented"):
    val doc = read(Paths.get("docs/lemma-bundles.md"))
    assert(doc.contains("Compatibility policy"))
    assert(doc.contains("major stdlib revision"))
