package sroof.checker

import sroof.core.{Term, CtorDef, IndDef, GlobalEnv, MatchCase, TerminationChecker}
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

  // ---- The guard used to have two holes, and either one proves False ----
  //
  // Measured on the previous tree: `sroof check` reported **OK, exit 0** on a
  // file whose only defspec was `Nat.zero = Nat.succ(Nat.zero)`. See
  // `cli/TerminationGateSuite`. These are the two shapes underneath.

  test("REJECT: the smaller argument is in a position the match did not take apart"):
    // fix f. λn. λm. match m { zero => zero; succ(k) => f(k, m) }
    //
    // `k` is a subterm of `m`, so the old rule ("some argument is smaller")
    // accepted it. But the argument that shrank is passed in *n*'s position
    // while `m` is handed straight back, so the very next match sees the same
    // `m` and this runs forever. Verified: it reached StackOverflowError.
    val loop = Term.Fix("f",
      Term.Pi("n", natTpe, Term.Pi("m", natTpe, natTpe)),
      Term.Lam("n", natTpe, Term.Lam("m", natTpe,
        Term.Mat(
          Term.Var(0), // m
          List(
            MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
            MatchCase("succ", 1,  // k = Var(0), m = Var(1), n = Var(2), f = Var(3)
              Term.App(Term.App(Term.Var(3), Term.Var(0)), Term.Var(1))  // f(k, m)
            ),
          ),
          natTpe,
        )
      ))
    )
    val result = TerminationChecker.check(loop)
    assert(result.isLeft, s"a non-terminating function was accepted: $result")

  test("REJECT: the recursive call is in the scrutinee"):
    // fix f. λn. match f(n) { zero => zero; succ(k) => zero }
    //
    // `checkBody` looked only at the branches, so a call with nothing guarding
    // it went unseen.
    val loop = Term.Fix("f",
      Term.Pi("n", natTpe, natTpe),
      Term.Lam("n", natTpe,
        Term.Mat(
          Term.App(Term.Var(1), Term.Var(0)),  // f(n)
          List(
            MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
            MatchCase("succ", 1, Term.Con("zero", "Nat", Nil)),
          ),
          natTpe,
        )
      ))
    val result = TerminationChecker.check(loop)
    assert(result.isLeft, s"a recursive call in the scrutinee was accepted: $result")

  test("REJECT: a recursive call in the scrutinee of a match with no cases"):
    // fix f. λn. match f(n) { }  — the shape that types as `Nat -> Empty`, and
    // from an `Empty` every proposition follows. There is no branch here, so a
    // traversal that only walks branches cannot see anything at all.
    val loop = Term.Fix("f",
      Term.Pi("n", natTpe, Term.Ind("Empty", Nil, Nil)),
      Term.Lam("n", natTpe,
        Term.Mat(Term.App(Term.Var(1), Term.Var(0)), Nil, Term.Ind("Empty", Nil, Nil))
      ))
    val result = TerminationChecker.check(loop)
    assert(result.isLeft, s"the route to a proof of False was accepted: $result")

  test("REJECT: the match takes apart something bound outside the fixpoint"):
    // A scrutinee that is not one of this function's own parameters gives no
    // decreasing position, so its constructor variables are not a measure.
    val loop = Term.Lam("outer", natTpe,
      Term.Fix("f",
        Term.Pi("n", natTpe, natTpe),
        Term.Lam("n", natTpe,
          Term.Mat(
            Term.Var(2), // outer
            List(
              MatchCase("zero", 0, Term.Con("zero", "Nat", Nil)),
              // k = Var(0), n = Var(1), f = Var(2), outer = Var(3)
              MatchCase("succ", 1, Term.App(Term.Var(2), Term.Var(0))),  // f(k)
            ),
            natTpe,
          )
        )))
    // `check` only inspects a top-level Fix, so hand it the Fix itself.
    val fix = loop.asInstanceOf[Term.Lam].body
    val result = TerminationChecker.check(fix)
    assert(result.isLeft, s"a measure taken from outside the fixpoint was accepted: $result")

  test("ACCEPT: recursion on the second argument still passes"):
    // The control. Pinning the decreasing position must not collapse into
    // "only the first argument may decrease" — this is the `matches(derive(r,c), t)`
    // shape the checker was written for, and it has to keep working.
    val f = Term.Fix("f",
      Term.Pi("r", natTpe, Term.Pi("t", natTpe, natTpe)),
      Term.Lam("r", natTpe, Term.Lam("t", natTpe,
        Term.Mat(
          Term.Var(0), // t
          List(
            MatchCase("zero", 0, Term.Var(1)),  // r
            MatchCase("succ", 1,  // k = Var(0), t = Var(1), r = Var(2), f = Var(3)
              // f(succ(r), k) — the first argument may even grow
              Term.App(
                Term.App(Term.Var(3), Term.Con("succ", "Nat", List(Term.Var(2)))),
                Term.Var(0))
            ),
          ),
          natTpe,
        )
      ))
    )
    val result = TerminationChecker.check(f)
    assert(result.isRight, s"a terminating function was rejected: $result")
