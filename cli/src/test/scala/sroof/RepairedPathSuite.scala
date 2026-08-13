package sroof

import munit.FunSuite

/** `sroof agent` must not write over the file it was given.
  *
  * The output path was `filePath.replaceAll("\\.sroof$", ".repaired.sroof")`,
  * which is the **identity** on any name not ending in `.sroof`. So
  * `sroof agent proof.txt` overwrote `proof.txt` — while printing "Repaired file
  * written to: proof.txt", which reads like a separate output. The original was
  * gone, with no backup and nothing to undo it.
  *
  * Nothing restricts the command to `.sroof` names, so reaching it needed only a
  * file called `proof.txt`, `nat.sroof.bak`, or a path with no extension.
  */
class RepairedPathSuite extends FunSuite:

  test("a .sroof name gets the repaired suffix"):
    assertEquals(Main.repairedPathFor("nat.sroof"), "nat.repaired.sroof")
    assertEquals(Main.repairedPathFor("/a/b/nat.sroof"), "/a/b/nat.repaired.sroof")

  test("a name that is not .sroof still gets a distinct output"):
    // The case that destroyed the input.
    assertEquals(Main.repairedPathFor("proof.txt"), "proof.txt.repaired.sroof")
    assertEquals(Main.repairedPathFor("nat.sroof.bak"), "nat.sroof.bak.repaired.sroof")
    assertEquals(Main.repairedPathFor("proof"), "proof.repaired.sroof")

  test("the output path is never the input path"):
    // The property, stated directly rather than as a list of examples — including
    // the ones that make a suffix rule tempting to get wrong.
    val names = List(
      "nat.sroof", "proof.txt", "proof", "nat.sroof.bak", ".sroof",
      "a.repaired.sroof", "/tmp/x", "/tmp/x.sroof", "sroof", "x.SROOF",
    )
    names.foreach { n =>
      assertNotEquals(Main.repairedPathFor(n), n, s"agent would overwrite its input: $n")
    }

  test("running twice does not clobber the first output"):
    val once  = Main.repairedPathFor("nat.sroof")
    val twice = Main.repairedPathFor(once)
    assertNotEquals(twice, once, "a second run would overwrite the first repaired file")
