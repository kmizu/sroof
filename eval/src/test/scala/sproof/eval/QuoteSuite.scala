package sproof.eval

import sproof.core.Term

class QuoteSuite extends munit.FunSuite:

  test("quote SUni(0) → Uni(0)"):
    assertEquals(Quote.quote(0, Semantic.SUni(0)), Term.Uni(0))

  test("quote SUni(3) → Uni(3)"):
    assertEquals(Quote.quote(0, Semantic.SUni(3)), Term.Uni(3))

  test("quote SCon(zero, Nat, []) → Con"):
    assertEquals(
      Quote.quote(0, Semantic.SCon("zero", "Nat", Nil)),
      Term.Con("zero", "Nat", Nil)
    )

  test("quote SNeu NVar: level=2 at size=3 → Var(0)"):
    val s = Semantic.SNeu(Neutral.NVar(2), Nil)
    assertEquals(Quote.quote(3, s), Term.Var(0))

  test("quote SNeu NVar: level=0 at size=1 → Var(0)"):
    val s = Semantic.SNeu(Neutral.NVar(0), Nil)
    assertEquals(Quote.quote(1, s), Term.Var(0))

  test("quote SLam: identity function roundtrips"):
    // Identity closure: v => v
    val s = Semantic.SLam("x", Semantic.SUni(0), v => v)
    Quote.quote(0, s) match
      case Term.Lam(_, Term.Uni(0), Term.Var(0)) => ()
      case other => fail(s"Expected Lam(_,Uni(0),Var(0)), got $other")

  test("normalize: Uni(0) is stable"):
    assertEquals(Quote.normalize(0, Nil, Term.Uni(0)), Term.Uni(0))

  test("normalize: identity app beta-reduces"):
    val t = Term.App(Term.Lam("x", Term.Uni(0), Term.Var(0)), Term.Uni(0))
    assertEquals(Quote.normalize(0, Nil, t), Term.Uni(0))

  test("normalize: K combinator reduces"):
    // K Uni(0) Uni(1) → Uni(0)
    val k = Term.Lam("x", Term.Uni(1), Term.Lam("y", Term.Uni(1), Term.Var(1)))
    val t = Term.App(Term.App(k, Term.Uni(0)), Term.Uni(1))
    assertEquals(Quote.normalize(0, Nil, t), Term.Uni(0))

  test("convEqual: same terms"):
    assert(Quote.convEqual(0, Nil, Term.Uni(0), Term.Uni(0)))

  test("convEqual: different universe levels differ"):
    assert(!Quote.convEqual(0, Nil, Term.Uni(0), Term.Uni(1)))

  test("convEqual: beta-equivalent terms"):
    val t1 = Term.App(Term.Lam("x", Term.Uni(0), Term.Var(0)), Term.Uni(0))
    val t2 = Term.Uni(0)
    assert(Quote.convEqual(0, Nil, t1, t2))

  test("alphaEq: Var same index"):
    assert(Quote.alphaEq(Term.Var(0), Term.Var(0)))

  test("alphaEq: Var different index"):
    assert(!Quote.alphaEq(Term.Var(0), Term.Var(1)))

  test("alphaEq: Lam ignores binder name"):
    val t1 = Term.Lam("x", Term.Uni(0), Term.Var(0))
    val t2 = Term.Lam("y", Term.Uni(0), Term.Var(0))
    assert(Quote.alphaEq(t1, t2))

  test("alphaEq: App with matching children"):
    assert(Quote.alphaEq(
      Term.App(Term.Var(0), Term.Uni(0)),
      Term.App(Term.Var(0), Term.Uni(0))
    ))
