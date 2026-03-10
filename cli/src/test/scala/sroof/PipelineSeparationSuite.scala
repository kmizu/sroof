package sroof

import munit.FunSuite
import sroof.core.GlobalEnv
import sroof.syntax.{ElabResult, Elaborator, Parser}

class PipelineSeparationSuite extends FunSuite:

  private def elaborate(src: String): ElabResult =
    val decls = Parser.parseProgram(src) match
      case Left(err) => fail(s"parse failed unexpectedly:\n$err")
      case Right(ds) => ds
    Elaborator.elaborate(decls) match
      case Left(err) => fail(s"elaboration failed unexpectedly: ${err.message}")
      case Right(r)  => r

  test("proof generation can succeed before kernel final validation rejects") {
    val source =
      """|inductive Nat {
         |  case zero: Nat
         |  case succ(n: Nat): Nat
         |}
         |defspec bad(n: Nat): n = Nat.zero {
         |  n
         |}
         |""".stripMargin

    val result = elaborate(source)
    given GlobalEnv = result.env

    val generated = Checker.generateProofCandidates(result)
    assert(generated.isRight, s"generation should succeed: $generated")
    val (candidates, _) = generated.toOption.get
    assertEquals(candidates.length, 1)

    val finalResult = Checker.finalizeProofCandidates(candidates)
    assert(finalResult.isLeft, s"kernel should reject invalid candidate: $finalResult")
    assert(finalResult.left.toOption.get.contains("Kernel rejected proof of 'bad'"))
  }

  test("checkAllWithWarnings still delegates final decision to kernel path") {
    val source =
      """|inductive Nat {
         |  case zero: Nat
         |  case succ(n: Nat): Nat
         |}
         |defspec bad(n: Nat): n = Nat.zero {
         |  n
         |}
         |""".stripMargin

    val result = elaborate(source)
    val checked = Checker.checkAllWithWarnings(result)
    assert(checked.isLeft, s"overall check should fail: $checked")
    assert(checked.left.toOption.get.contains("Kernel rejected proof of 'bad'"))
  }

  test("valid theorem passes generation and final validation") {
    val source =
      """|inductive Nat {
         |  case zero: Nat
         |  case succ(n: Nat): Nat
         |}
         |defspec refl(n: Nat): n = n {
         |  by trivial
         |}
         |""".stripMargin

    val result = elaborate(source)
    given GlobalEnv = result.env

    val generated = Checker.generateProofCandidates(result)
    assert(generated.isRight, s"generation should succeed: $generated")
    val (candidates, warnings) = generated.toOption.get
    assert(warnings.isEmpty, s"valid proof should not emit warnings: $warnings")

    val finalResult = Checker.finalizeProofCandidates(candidates)
    assert(finalResult.isRight, s"kernel should accept valid candidate: $finalResult")
  }

