package sroof.it

import munit.FunSuite
import java.nio.file.{Files, Paths}
import sroof.extract.Extractor
import sroof.syntax.{Parser, Elaborator}

/** Does the extracted Scala compute what the `.sroof` file says?
  *
  * `ExtractionCorpusSuite` shows the output compiles. Compiling is a weak bar: an
  * extractor that swapped a constructor's two arguments, dropped a match branch, or
  * mixed up which recursive call it was making would compile just as happily. These
  * cases build the data, run the extracted function, and check the answer.
  *
  * Every driver goes through the extracted definitions only — nothing here
  * re-implements what it is testing.
  */
class ExtractionRuntimeSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(600, "s")

  private def extractOf(path: String): String =
    val src = Files.readString(Paths.get(path))
    val out = for
      d <- Parser.parseProgram(src).left.map(_.toString)
      r <- Elaborator.elaborate(d).left.map(_.message)
    yield Extractor.extractProgram(r.env)
    out.fold(e => fail(s"$path: extraction failed: $e"), identity)

  private def run(path: String, driver: String): String =
    val (result, value) = CompilerHarness.compileAndInvoke(
      extractOf(path) + "\n\n" + driver, "Driver", "check")
    assert(!result.failed, s"$path: the extraction did not compile:\n${result.report}")
    value.fold(fail("no value returned"))(_.toString)

  /** Nat ⇄ Int, so a Peano result can be stated as a number. */
  private val natBridge =
    """|  def toInt(n: Nat): Int = n match
       |    case Nat.Zero    => 0
       |    case Nat.Succ(k) => 1 + toInt(k)
       |  def nat(i: Int): Nat = if i <= 0 then Nat.Zero else Nat.Succ(nat(i - 1))
       |""".stripMargin

  test("extracted addition adds"):
    // Asymmetric arguments: `plus(2, 3)` and `plus(3, 2)` agree, but a extractor that
    // recursed on the wrong argument would not terminate or would return 3.
    val out = run("examples/nat.sroof",
      s"""|object Driver:
          |$natBridge
          |  def check(): String =
          |    List(
          |      toInt(plus(nat(2))(nat(3))),
          |      toInt(plus(nat(0))(nat(4))),
          |      toInt(plus(nat(4))(nat(0))),
          |    ).mkString(",")
          |""".stripMargin)
    assertEquals(out, "5,4,4")

  test("extracted polymorphic list functions compute"):
    // `poly_length` is the definition v0.19 could not extract at all: its element
    // type is an ordinary `Type`-valued parameter in the source, and it has to come
    // out as a Scala type parameter.
    val out = run("stdlib/PolyList.sroof",
      s"""|object Driver:
          |$natBridge
          |  val xs: PolyList[Nat] =
          |    PolyList.Cons(nat(1), PolyList.Cons(nat(2), PolyList.Cons(nat(3), PolyList.Nil)))
          |  def ints(l: PolyList[Nat]): List[Int] = l match
          |    case PolyList.Nil        => List()
          |    case PolyList.Cons(h, t) => toInt(h) :: ints(t)
          |  def check(): String =
          |    List(
          |      toInt(poly_length(xs)).toString,
          |      ints(poly_reverse(xs)).mkString("-"),
          |      ints(poly_append(xs)(xs)).mkString("-"),
          |    ).mkString(",")
          |""".stripMargin)
    // reverse is what pins argument order: a `Cons` built the other way round would
    // give back the input unchanged.
    assertEquals(out, "3,3-2-1,1-2-3-1-2-3")

  test("extracted vector concatenation keeps the elements in order"):
    // Vec carries its length as a constructor field. Erasing that field — which the
    // extractor did until the field turned out to be what `concat` passes to itself —
    // makes this program fail to compile rather than give a wrong answer.
    val out = run("stdlib/Vec.sroof",
      s"""|object Driver:
          |$natBridge
          |  def v(xs: List[Int]): Vec[Nat] =
          |    xs.foldRight(Vec.Nil: Vec[Nat])((x, acc) => Vec.Cons(len(acc), nat(x), acc))
          |  def len(x: Vec[Nat]): Nat = x match
          |    case Vec.Nil           => Nat.Zero
          |    case Vec.Cons(n, _, _) => Nat.Succ(n)
          |  def ints(x: Vec[Nat]): List[Int] = x match
          |    case Vec.Nil              => List()
          |    case Vec.Cons(_, h, tail) => toInt(h) :: ints(tail)
          |  def check(): String =
          |    ints(concat(nat(2))(nat(1))(v(List(1, 2)))(v(List(3)))).mkString("-")
          |""".stripMargin)
    assertEquals(out, "1-2-3")
