package sproof.core

class SubstSuite extends munit.FunSuite:

  test("shift: universe is unchanged"):
    assertEquals(Subst.shift(1, Term.Uni(0)), Term.Uni(0))

  test("shift: Var(0) → Var(1)"):
    assertEquals(Subst.shift(1, Term.Var(0)), Term.Var(1))

  test("shift: Var(2) → Var(3) with d=1"):
    assertEquals(Subst.shift(1, Term.Var(2)), Term.Var(3))

  test("shift: bound var in Lam stays bound"):
    // Inside Lam, cutoff rises to 1, so Var(0) (bound) is unchanged
    val t = Term.Lam("x", Term.Uni(0), Term.Var(0))
    assertEquals(Subst.shift(1, t), Term.Lam("x", Term.Uni(0), Term.Var(0)))

  test("shift: free Var(1) under Lam gets shifted"):
    // Inside Lam, cutoff = 1; Var(1) ≥ 1, so becomes Var(2)
    val t = Term.Lam("x", Term.Uni(0), Term.Var(1))
    assertEquals(Subst.shift(1, t), Term.Lam("x", Term.Uni(0), Term.Var(2)))

  test("shift: nested Pi both sides"):
    val t = Term.Pi("x", Term.Var(0), Term.Var(2))
    val r = Subst.shift(1, t)
    assertEquals(r, Term.Pi("x", Term.Var(1), Term.Var(3)))

  test("subst: replace Var(0) with Uni(0)"):
    assertEquals(Subst.subst(Term.Uni(0), Term.Var(0)), Term.Uni(0))

  test("subst: Var(1) > 0 becomes Var(0) (shift down)"):
    assertEquals(Subst.subst(Term.Uni(0), Term.Var(1)), Term.Var(0))

  test("subst: Var(0) < 0 impossible; index exactly 0 replaced"):
    val body = Term.App(Term.Var(0), Term.Var(1))
    val r    = Subst.subst(Term.Uni(0), body)
    assertEquals(r, Term.App(Term.Uni(0), Term.Var(0)))

  test("subst: inside Lam, index shifts up by 1"):
    // Lam body Var(0) is bound; Var(1) refers to the outer var being substituted
    val body = Term.Lam("y", Term.Uni(0), Term.Var(1))
    val r    = Subst.subst(Term.Uni(0), body)
    assertEquals(r, Term.Lam("y", Term.Uni(0), Term.Uni(0)))

  test("shiftFrom: cutoff below var"):
    assertEquals(Subst.shiftFrom(1, 1, Term.Var(0)), Term.Var(0))  // 0 < cutoff=1: unchanged
    assertEquals(Subst.shiftFrom(1, 1, Term.Var(1)), Term.Var(2))  // 1 >= cutoff=1: +1

  test("subst: App with no occurrence of 0"):
    val t = Term.App(Term.Var(1), Term.Var(2))
    // No Var(0); Var(1)→Var(0), Var(2)→Var(1)
    assertEquals(Subst.subst(Term.Uni(0), t), Term.App(Term.Var(0), Term.Var(1)))

  test("substN: substitute index 1"):
    val t = Term.App(Term.Var(0), Term.Var(1))
    // index 1 → Uni(0) (shifted by 1 = still Uni(0)); index 0 unchanged; index > 1 decremented
    assertEquals(Subst.substN(Term.Uni(0), 1, t), Term.App(Term.Var(0), Term.Uni(0)))
