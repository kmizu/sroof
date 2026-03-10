package sroof

import java.nio.file.{Files, Paths}
import munit.FunSuite

/** Verifies that the programmer-oriented examples check successfully.
 *
 *  These examples demonstrate sroof applied to everyday data-structure and
 *  algorithm verification tasks a Scala programmer would recognise.
 */
class PracticalExamplesSuite extends FunSuite:

  private def read(path: String): String =
    Files.readString(Paths.get(path))

  private def checkFile(path: String): Unit =
    val src = read(path)
    val result = Main.processSource(src, path)
    assert(result.isRight, s"example should check successfully: $path -> $result")

  test("verified_stack.sroof checks successfully"):
    checkFile("examples/verified_stack.sroof")

  test("verified_ordering.sroof checks successfully"):
    checkFile("examples/verified_ordering.sroof")

  test("safe_division.sroof checks successfully"):
    checkFile("examples/safe_division.sroof")
