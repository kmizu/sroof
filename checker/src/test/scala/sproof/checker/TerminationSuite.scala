package sproof.checker

import sproof.core.{Term, CtorDef, IndDef, GlobalEnv, MatchCase, TerminationChecker}
import munit.FunSuite

/** Tests for structural termination checking of Fix (recursive functions).
 *
 *  A recursive function `fix f. λx. body` terminates if every recursive call
 *  to `f` in `body` is applied to a structurally smaller argument — i.e., a
 *  variable bound by a pattern match on the decreasing argument.
 *
 *  Without termination checking, non-terminating functions make the NbE
 *  evaluator diverge, which can be exploited to prove False.
 */
class TerminationSuite extends FunSuite:

  given GlobalEnv = GlobalEnv.withNat
  val natTpe = Term.Ind("Nat", Nil, Nil)

  // ---- Should pass termination check ----

  test("plus(n, m) terminates — recursive call on pattern-matched subterm"):
    // fix plus. λn. λm. match n { zero => m; succ(k) => succ(plus(k, m)) }
    // plus = Var(2), n = Var(1), m = Var(0), k = Var(0) in succ branch
    val plus = Term.Fix("plus",
      Term.Pi("n", natTpe, Term.Pi("m", natTpe, natTpe)),
      Term.Lam("n", natTpe, Term.Lam("m", natTpe,
        Term.Mat(
          Term.Var(1), // n
          List(
            MatchCase("zero", 0, Term.Var(0)),  // m
            MatchCase("succ", 1,  // k = Var(0), m = Var(1), n = Var(2), plus = Var(3)
              Term.Con("succ", "Nat", List(
                Term.App(Term.App(Term.Var(3), Term.Var(0)), Term.Var(1))  // plus(k, m)
              ))
            ),
          ),
          natTpe,
        )
      ))
    )
    val result = TerminationChecker.check(plus)
    assert(result.isRight, s"Expected Right, got $result")

  test("pred(n) terminates — base case returns zero, recursive case returns subterm"):
    // fix pred. λn. match n { zero => zero; succ(k) => k }
    val pred = Term.Fix("pred",
      Term.Pi("n", natTpe, natTpe),
      Term.Lam("n", natTpe,
        Term.Mat(
          Term.Var(0), // n
          List(
            MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
            MatchCase("succ", 1, Term.Var(0)),  // k
          ),
          natTpe,
        )
      )
    )
    val result = TerminationChecker.check(pred)
    assert(result.isRight, s"Expected Right, got $result")

  test("non-recursive Fix passes trivially"):
    // fix id. λn. n  (no recursive call)
    val idFn = Term.Fix("id",
      Term.Pi("n", natTpe, natTpe),
      Term.Lam("n", natTpe, Term.Var(0))
    )
    val result = TerminationChecker.check(idFn)
    assert(result.isRight, s"Expected Right, got $result")

  test("non-Fix terms pass trivially"):
    val result = TerminationChecker.check(Term.Lam("x", natTpe, Term.Var(0)))
    assert(result.isRight)

  // ---- Should fail termination check ----

  test("REJECT: direct infinite loop — fix f. λn. f(n)"):
    // Recursive call on the same argument, not a structurally smaller one
    val loop = Term.Fix("f",
      Term.Pi("n", natTpe, natTpe),
      Term.Lam("n", natTpe,
        Term.App(Term.Var(1), Term.Var(0))  // f(n)
      )
    )
    val result = TerminationChecker.check(loop)
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("REJECT: recursive call on non-subterm — fix f. λn. f(succ(n))"):
    val loop = Term.Fix("f",
      Term.Pi("n", natTpe, natTpe),
      Term.Lam("n", natTpe,
        Term.App(Term.Var(1), Term.Con("succ", "Nat", List(Term.Var(0))))  // f(succ(n))
      )
    )
    val result = TerminationChecker.check(loop)
    assert(result.isLeft, s"Expected Left (rejected), got $result")

  test("REJECT: no argument — fix f. f"):
    // fix f. f  (self-application with no argument)
    val loop = Term.Fix("f",
      natTpe,
      Term.Var(0)  // f
    )
    val result = TerminationChecker.check(loop)
    assert(result.isLeft, s"Expected Left (rejected), got $result")
