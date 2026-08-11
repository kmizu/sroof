package sroof.it

import munit.FunSuite
import sroof.extract.Extractor
import sroof.syntax.{Parser, Elaborator}

/** Extracted Scala must compile and compute.
  *
  * `ExtractorSuite` asserts on substrings — `contains("enum Nat:")` and the like —
  * which is why output that was not valid Scala shipped for a long time. Nothing
  * ever fed the result to a compiler. This does.
  *
  * The two defects it would have caught: patterns emitted as `case _.Zero`, where
  * `_` is not a stable identifier, and a `Fix` rendered as `def f: Any = …`, which
  * makes the recursive call inside it untypeable.
  */
class ExtractionCompilesSuite extends FunSuite:

  override val munitTimeout = scala.concurrent.duration.Duration(300, "s")

  private def extract(src: String): String =
    val out = for
      decls <- Parser.parseProgram(src).left.map(_.toString)
      res   <- Elaborator.elaborate(decls).left.map(_.message)
    yield Extractor.extractProgram(res.env)
    out.fold(e => fail(s"extraction failed: $e"), identity)

  test("extracted arithmetic compiles and computes"):
    // `sub` is deliberately asymmetric — it matches on its *second* argument and
    // returns its first — so an extraction that swapped them would still compile
    // and the runtime assertion would catch it.
    val extracted = extract(
      """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
         |def plus(a: Nat, b: Nat): Nat {
         |  match a {
         |    case Nat.zero    => b
         |    case Nat.succ(k) => Nat.succ(plus(k, b))
         |  }
         |}
         |def sub(a: Nat, b: Nat): Nat {
         |  match b {
         |    case Nat.zero    => a
         |    case Nat.succ(k) => Nat.zero
         |  }
         |}
         |""".stripMargin)

    val driver =
      """|
         |@main def run(): Unit =
         |  val one = Nat.Succ(Nat.Zero)
         |  assert(plus(one)(one) == Nat.Succ(Nat.Succ(Nat.Zero)), "plus")
         |  assert(sub(one)(Nat.Zero) == one,                      "sub keeps its first argument")
         |  assert(sub(Nat.Zero)(one) == Nat.Zero,                 "sub is not symmetric")
         |""".stripMargin

    val r = CompilerHarness.compile("Extracted.scala" -> (extracted + driver))
    assert(!r.failed, s"extracted Scala must compile:\n$extracted\n---\n${r.report}")

  test("a theorem erases to a Unit-valued definition that still compiles"):
    val extracted = extract(
      """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
         |def plus(a: Nat, b: Nat): Nat {
         |  match a {
         |    case Nat.zero    => b
         |    case Nat.succ(k) => Nat.succ(plus(k, b))
         |  }
         |}
         |defspec plus_zero_left(n: Nat): plus(Nat.zero, n) = n { by trivial }
         |""".stripMargin)
    val r = CompilerHarness.compile("Erased.scala" -> extracted)
    assert(!r.failed, s"extracted Scala must compile:\n$extracted\n---\n${r.report}")
