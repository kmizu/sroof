package sroof.eval

import sroof.core.Term

class EvalSuite extends munit.FunSuite:

  test("eval Uni(0)"):
    assertEquals(Eval.eval(Nil, Term.Uni(0)), Semantic.SUni(0))

  test("eval Var(0) from singleton env"):
    assertEquals(Eval.eval(List(Semantic.SUni(0)), Term.Var(0)), Semantic.SUni(0))

  test("eval Var(1) from env of two"):
    val env = List(Semantic.SUni(1), Semantic.SUni(0))
    assertEquals(Eval.eval(env, Term.Var(1)), Semantic.SUni(0))

  test("eval Lam returns SLam"):
    val t = Term.Lam("x", Term.Uni(0), Term.Var(0))
    assert(Eval.eval(Nil, t).isInstanceOf[Semantic.SLam])

  test("eval App(identity, Uni(0)) = Uni(0)"):
    val id  = Term.Lam("x", Term.Uni(0), Term.Var(0))
    val app = Term.App(id, Term.Uni(0))
    assertEquals(Eval.eval(Nil, app), Semantic.SUni(0))

  test("eval App(K combinator): K Uni(0) Uni(1) = Uni(0)"):
    // K = λx. λy. x  where x is at index 1 under the y-binder
    val k = Term.Lam("x", Term.Uni(1), Term.Lam("y", Term.Uni(1), Term.Var(1)))
    val r = Eval.eval(Nil, Term.App(Term.App(k, Term.Uni(0)), Term.Uni(1)))
    assertEquals(r, Semantic.SUni(0))

  test("eval Pi returns SPi"):
    assert(Eval.eval(Nil, Term.Pi("x", Term.Uni(0), Term.Uni(0))).isInstanceOf[Semantic.SPi])

  test("eval Let substitutes correctly"):
    // let _ : Type1 = Type0 in Var(0) ≡ Type0
    val t = Term.Let("x", Term.Uni(1), Term.Uni(0), Term.Var(0))
    assertEquals(Eval.eval(Nil, t), Semantic.SUni(0))

  test("eval Con with no args"):
    val t = Term.Con("zero", "Nat", Nil)
    assertEquals(Eval.eval(Nil, t), Semantic.SCon("zero", "Nat", Nil))

  test("eval Con with args"):
    val t = Term.Con("succ", "Nat", List(Term.Con("zero", "Nat", Nil)))
    assertEquals(
      Eval.eval(Nil, t),
      Semantic.SCon("succ", "Nat", List(Semantic.SCon("zero", "Nat", Nil)))
    )

  test("eval Mat on SCon: selects correct branch"):
    import sroof.core.MatchCase
    val zero = Term.Con("zero", "Nat", Nil)
    val cases = List(
      MatchCase("zero", 0, Term.Uni(0)),
      MatchCase("succ", 1, Term.Uni(1)),
    )
    val mat = Term.Mat(zero, cases, Term.Uni(0))
    assertEquals(Eval.eval(Nil, mat), Semantic.SUni(0))

  test("eval Mat on SCon succ: selects succ branch and binds arg"):
    import sroof.core.MatchCase
    val one = Term.Con("succ", "Nat", List(Term.Con("zero", "Nat", Nil)))
    val cases = List(
      MatchCase("zero", 0, Term.Uni(99)),
      // succ binds 1 var; body Var(0) refers to the predecessor
      MatchCase("succ", 1, Term.Var(0)),
    )
    val mat = Term.Mat(one, cases, Term.Uni(0))
    assertEquals(Eval.eval(Nil, mat), Semantic.SCon("zero", "Nat", Nil))
