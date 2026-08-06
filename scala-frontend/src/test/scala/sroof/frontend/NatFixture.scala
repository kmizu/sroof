package sroof.frontend

/** Hand-built IR for the `Nat` proof module.
 *
 *  This is the exact IR the compiler plugin is expected to extract from
 *  `examples-scala3/.../NatProofs.scala`.  Keeping it here lets the translation
 *  and proof layers be tested without a compiler in the loop; the integration
 *  tests then check that the plugin really does produce this shape.
 */
object NatFixture:

  private val sp = SourceSpan.synthetic

  def sym(s: String): SymbolId = SymbolId(s)

  val natId   = sym("NatProofs.Nat")
  val zeroId  = sym("NatProofs.Nat.Zero")
  val succId  = sym("NatProofs.Nat.Succ")
  val plusId  = sym("NatProofs.plus")

  val natTpe: ResolvedType = ResolvedType.Inductive(natId, "Nat")

  val zeroCtor = ResolvedConstructor(zeroId, "Zero", Nil, sp)
  val succCtor = ResolvedConstructor(
    succId, "Succ", List(ResolvedBinder(sym("Nat.Succ.n"), "n", natTpe)), sp)

  val natInd = ResolvedInductive(natId, "Nat", List(zeroCtor, succCtor), sp)

  def local(id: String, name: String): ResolvedExpr =
    ResolvedExpr.Local(sym(id), name, sp)

  val zero: ResolvedExpr = ResolvedExpr.Construct(natId, zeroId, "Zero", Nil, sp)

  def succ(arg: ResolvedExpr): ResolvedExpr =
    ResolvedExpr.Construct(natId, succId, "Succ", List(arg), sp)

  def plus(a: ResolvedExpr, b: ResolvedExpr): ResolvedExpr =
    ResolvedExpr.Call(plusId, "plus", List(a, b), sp)

  private val pn = ResolvedBinder(sym("plus.n"), "n", natTpe)
  private val pm = ResolvedBinder(sym("plus.m"), "m", natTpe)
  private val pk = ResolvedBinder(sym("plus.k"), "k", natTpe)

  /** def plus(n: Nat, m: Nat): Nat = n match { case Zero => m; case Succ(k) => Succ(plus(k, m)) } */
  val plusDef = ResolvedDef(
    id     = plusId,
    name   = "plus",
    params = List(pn, pm),
    result = natTpe,
    body   = ResolvedExpr.Match(
      local("plus.n", "n"),
      List(
        ResolvedCase(zeroId, "Zero", Nil, local("plus.m", "m"), sp),
        ResolvedCase(succId, "Succ", List(pk),
          succ(plus(local("plus.k", "k"), local("plus.m", "m"))), sp),
      ),
      sp, natTpe),
    span   = sp,
  )

  private def theorem(
    name:   String,
    params: List[ResolvedBinder],
    lhs:    ResolvedExpr,
    rhs:    ResolvedExpr,
    tactic: ResolvedTactic,
  ) = ResolvedTheorem(
    sym(s"NatProofs.$name"), name, params,
    ResolvedProp(natTpe, lhs, rhs, sp), tactic, isSimp = false, sp)

  private val tn = ResolvedBinder(sym("th.n"), "n", natTpe)
  private val tm = ResolvedBinder(sym("th.m"), "m", natTpe)
  private val tk = ResolvedBinder(sym("th.k"), "k", natTpe)

  val plusZeroLeft = theorem("plusZeroLeft", List(tm),
    plus(zero, local("th.m", "m")), local("th.m", "m"), ResolvedTactic.Trivial(sp))

  val plusSuccLeft = theorem("plusSuccLeft", List(tn, tm),
    plus(succ(local("th.n", "n")), local("th.m", "m")),
    succ(plus(local("th.n", "n"), local("th.m", "m"))),
    ResolvedTactic.Trivial(sp))

  val reflTheorem = theorem("refl", List(tn),
    local("th.n", "n"), local("th.n", "n"),
    ResolvedTactic.Induction(sym("th.n"), "n", List(
      ResolvedTacticCase(zeroId, "Zero", Nil, usesIh = false, ResolvedTactic.Trivial(sp), sp),
      ResolvedTacticCase(succId, "Succ", List(tk), usesIh = false, ResolvedTactic.Trivial(sp), sp),
    ), sp))

  val plusZeroRight = theorem("plusZeroRight", List(tn),
    plus(local("th.n", "n"), zero), local("th.n", "n"),
    ResolvedTactic.Induction(sym("th.n"), "n", List(
      ResolvedTacticCase(zeroId, "Zero", Nil, usesIh = false, ResolvedTactic.Trivial(sp), sp),
      ResolvedTacticCase(succId, "Succ", List(tk), usesIh = true,
        ResolvedTactic.Simplify(
          List(ResolvedLemmaRef.InductionHypothesis(sym("th.k"), "k", sp)), sp), sp),
    ), sp))

  val module = ResolvedModule(
    sym("NatProofs"), "NatProofs",
    List(natInd), List(plusDef),
    List(plusZeroLeft, plusSuccLeft, reflTheorem, plusZeroRight),
    sp)
