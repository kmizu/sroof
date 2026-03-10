package sroof

import java.nio.file.{Files, Paths}
import munit.FunSuite

class StdlibSuite extends FunSuite:

  private def read(path: String): String =
    Files.readString(Paths.get(path))

  test("stdlib v1 files parse/elaborate/check successfully"):
    val files = List(
      "stdlib/Nat.sroof",
      "stdlib/List.sroof",
      "stdlib/Vec.sroof",
      "stdlib/Bool.sroof",
      "stdlib/Relation.sroof",
      "stdlib/Effect.sroof",
      "stdlib/Dictionary.sroof",
      "stdlib/Option.sroof",
      "stdlib/Either.sroof",
      "stdlib/Pair.sroof",
      "stdlib/PolyList.sroof",
      "stdlib/Char.sroof",
      "stdlib/String.sroof",
      "stdlib/Sigma.sroof",
      "stdlib/Regex.sroof",
    )
    files.foreach { file =>
      val src = read(file)
      val result = Main.processSource(src, file)
      assert(result.isRight, s"stdlib file should pass checker: $file -> $result")
    }

  test("usage examples consume stdlib declarations directly (concatenated source)"):
    val pairs = List(
      ("stdlib/Nat.sroof", "examples/stdlib/nat_usage.sroof"),
      ("stdlib/List.sroof", "examples/stdlib/list_usage.sroof"),
      ("stdlib/Vec.sroof", "examples/stdlib/vec_usage.sroof"),
      ("stdlib/Bool.sroof", "examples/stdlib/bool_usage.sroof"),
      ("stdlib/Relation.sroof", "examples/stdlib/relation_usage.sroof"),
      ("stdlib/Effect.sroof", "examples/stdlib/effect_usage.sroof"),
      ("stdlib/Dictionary.sroof", "examples/stdlib/dictionary_usage.sroof"),
      ("stdlib/Option.sroof", "examples/stdlib/option_usage.sroof"),
      ("stdlib/Either.sroof", "examples/stdlib/either_usage.sroof"),
      ("stdlib/Pair.sroof", "examples/stdlib/pair_usage.sroof"),
      ("stdlib/PolyList.sroof", "examples/stdlib/polylist_usage.sroof"),
      ("stdlib/Char.sroof", "examples/stdlib/char_usage.sroof"),
      ("stdlib/String.sroof", "examples/stdlib/string_usage.sroof"),
      ("stdlib/Sigma.sroof", "examples/stdlib/sigma_usage.sroof"),
      ("stdlib/Regex.sroof", "examples/stdlib/regex_usage.sroof"),
    )
    pairs.foreach { (lib, usage) =>
      val src = read(lib) + "\n\n" + read(usage)
      val result = Main.processSource(src, s"$lib + $usage")
      assert(result.isRight, s"usage should type-check with stdlib declarations: $lib + $usage -> $result")
    }

  test("stdlib naming/layout conventions are documented"):
    val doc = read("docs/stdlib.md")
    assert(doc.contains("stdlib/Nat.sroof"))
    assert(doc.contains("stdlib/List.sroof"))
    assert(doc.contains("stdlib/Vec.sroof"))
    assert(doc.contains("stdlib/Bool.sroof"))
    assert(doc.contains("stdlib/Relation.sroof"))
    assert(doc.contains("stdlib/Effect.sroof"))
    assert(doc.contains("stdlib/Dictionary.sroof"))
    assert(doc.contains("stdlib/Option.sroof"))
    assert(doc.contains("stdlib/Either.sroof"))
    assert(doc.contains("stdlib/Pair.sroof"))
    assert(doc.contains("stdlib/PolyList.sroof"))
    assert(doc.contains("stdlib/Char.sroof"))
    assert(doc.contains("stdlib/String.sroof"))
    assert(doc.contains("stdlib/Sigma.sroof"))
    assert(doc.contains("stdlib/Regex.sroof"))
