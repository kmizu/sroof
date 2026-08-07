package sroof

import munit.FunSuite

/** Indexed families: a constructor's declared index must be respected.
  *
  * Every `SOUNDNESS` test in this file reported `OK` on the v0.9 tree. That is
  * what makes them worth having: `IndChecker.inferConWithParams` used to return
  * the expected type's own spine, so the conversion check at the call site
  * compared the expected type with itself and accepted any index.
  *
  * Each rejection is asserted to be a *type* error rather than merely a `Left`.
  * A syntax error is also a `Left`, and a test that accepted one would keep
  * passing after someone broke the feature it is guarding.
  */
class IndexedFamilySuite extends FunSuite:

  /** `Vec` with real indices: `vnil` is length zero, `vcons` adds one. */
  private val vec =
    """|inductive Nat {
       |  case zero: Nat
       |  case succ(n: Nat): Nat
       |}
       |
       |inductive Vec(A: Type)(n: Nat) {
       |  case vnil: Vec(A)(Nat.zero)
       |  case vcons(m: Nat, head: A, tail: Vec(A)(m)): Vec(A)(Nat.succ(m))
       |}
       |""".stripMargin

  private def check(body: String): Either[String, ?] =
    Main.processSource(vec + body, "indexed.sroof")

  private def assertTypeError(body: String, clue: String): Unit =
    val result = check(body)
    assert(result.isLeft, s"$clue — expected rejection, got: $result")
    val msg = result.swap.toOption.get
    assert(
      msg.contains("Type mismatch") || msg.contains("mismatch"),
      s"$clue — rejected, but not as a type error. A parse error would also be a " +
        s"Left and would make this test vacuous. Message was: $msg",
    )

  // ---- accepted ----

  test("vnil has length zero"):
    val r = check("defspec t: Vec(Nat)(Nat.zero) { Vec.vnil }")
    assert(r.isRight, s"expected acceptance, got: $r")

  test("vcons onto vnil has length one"):
    val r = check(
      "defspec t: Vec(Nat)(Nat.succ(Nat.zero)) { Vec.vcons(Nat.zero, Nat.zero, Vec.vnil) }"
    )
    assert(r.isRight, s"expected acceptance, got: $r")

  test("nesting: two vcons have length two"):
    val r = check(
      """|defspec t: Vec(Nat)(Nat.succ(Nat.succ(Nat.zero))) {
         |  Vec.vcons(Nat.succ(Nat.zero), Nat.zero,
         |    Vec.vcons(Nat.zero, Nat.zero, Vec.vnil))
         |}
         |""".stripMargin
    )
    assert(r.isRight, s"expected acceptance, got: $r")

  // ---- rejected ----

  test("SOUNDNESS: vnil is not a length-one vector"):
    assertTypeError(
      "defspec t: Vec(Nat)(Nat.succ(Nat.zero)) { Vec.vnil }",
      "the empty vector claimed as length one",
    )

  test("SOUNDNESS: one vcons is not a length-two vector"):
    assertTypeError(
      """|defspec t: Vec(Nat)(Nat.succ(Nat.succ(Nat.zero))) {
         |  Vec.vcons(Nat.zero, Nat.zero, Vec.vnil)
         |}
         |""".stripMargin,
      "a one-element vector claimed as length two",
    )

  test("SOUNDNESS: the tail's index is checked too"):
    // The outer index is consistent with `m = succ zero`, so only the *tail*
    // is wrong. This separates the argument check from the return-index check:
    // deriving the return index correctly but skipping the arguments would
    // still accept this.
    assertTypeError(
      """|defspec t: Vec(Nat)(Nat.succ(Nat.succ(Nat.zero))) {
         |  Vec.vcons(Nat.succ(Nat.zero), Nat.zero, Vec.vnil)
         |}
         |""".stripMargin,
      "a length-zero tail supplied where length one was required",
    )

  test("the element type is still checked (control)"):
    // This one failed before v0.10 as well. It is here so that a regression
    // which broke argument checking outright would be distinguishable from one
    // that only broke index checking.
    assertTypeError(
      """|inductive Bool { case tru: Bool  case fls: Bool }
         |defspec t: Vec(Nat)(Nat.succ(Nat.zero)) {
         |  Vec.vcons(Nat.zero, Bool.tru, Vec.vnil)
         |}
         |""".stripMargin,
      "a Bool element in a Vec of Nat",
    )

  test("a constructor may not claim an arbitrary index"):
    // `Bad(A)(n)` says "anylen has whatever length you wanted", which would make
    // the conversion check compare the expected type with itself. Rejected at
    // use, with a message that names the declaration rather than the use site.
    val source =
      """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
         |inductive Bad(A: Type)(n: Nat) {
         |  case anylen: Bad(A)(n)
         |  case one(head: A): Bad(A)(Nat.succ(Nat.zero))
         |}
         |defspec t: Bad(Nat)(Nat.succ(Nat.zero)) { Bad.anylen }
         |""".stripMargin
    val result = Main.processSource(source, "bad.sroof")
    assert(result.isLeft, s"expected rejection, got: $result")
    val msg = result.swap.toOption.get
    assert(
      msg.contains("own index variable"),
      s"expected the declaration to be named as the problem, got: $msg",
    )

  // ---- the shipped example ----

  test("examples/vec_indexed.sroof checks"):
    val path   = "examples/vec_indexed.sroof"
    val src    = java.nio.file.Files.readString(java.nio.file.Paths.get(path))
    val result = Main.processSource(src, path)
    assert(result.isRight, s"example should check successfully: $path -> $result")

  // ---- case analysis refines the index (v0.12) ----

  /** `vlen` reads the length off the constructor, so no recursion and no IH. */
  private val vlenDef =
    """|def vlen(A: Type, n: Nat, v: Vec(A)(n)): Nat {
       |  match v {
       |    case Vec.vnil           => Nat.zero
       |    case Vec.vcons(m, h, t) => Nat.succ(m)
       |  }
       |}
       |""".stripMargin

  test("cases on a Vec proves the length matches the index"):
    // Only provable if each branch learns its index: `vnil` must be asked for
    // `vlen A zero vnil = zero`, not `vlen A n vnil = n`.
    val r = Main.processSource(
      vec + vlenDef +
        """|defspec vlen_matches(A: Type, n: Nat, v: Vec(A)(n)): vlen(A, n, v) = n {
           |  by cases v { case vnil => trivial  case vcons m h t => trivial }
           |}
           |""".stripMargin,
      "vlen.sroof",
    )
    assert(r.isRight, s"expected acceptance, got: $r")

  test("induction without an IH refines the index the same way"):
    // `induction` with no case requesting an IH goes through the same plain `Mat`
    // path as `cases`, so it must agree.
    val r = Main.processSource(
      vec + vlenDef +
        """|defspec vlen_matches2(A: Type, n: Nat, v: Vec(A)(n)): vlen(A, n, v) = n {
           |  by induction v { case vnil => trivial  case vcons m h t => trivial }
           |}
           |""".stripMargin,
      "vlen2.sroof",
    )
    assert(r.isRight, s"expected acceptance, got: $r")

  test("SOUNDNESS: refinement does not make a false claim provable"):
    // The `vnil` branch really does become `zero = zero` and closes. The point is
    // that `vcons` becomes `succ m = zero` and does not — refining one branch must
    // not excuse the others.
    val r = Main.processSource(
      vec +
        """|defspec bad(A: Type, n: Nat, v: Vec(A)(n)): n = Nat.zero {
           |  by cases v { case vnil => trivial  case vcons m h t => trivial }
           |}
           |""".stripMargin,
      "bad.sroof",
    )
    assert(r.isLeft, s"`n = zero` is false and must be rejected, got: $r")
    assert(
      r.swap.toOption.get.contains("succ"),
      s"it must fail in the vcons branch, on `succ m = zero`; got: ${r.swap.toOption.get}",
    )

  test("SOUNDNESS: an absurd equation is not provable by matching"):
    val r = Main.processSource(
      vec +
        """|defspec bad(A: Type, n: Nat, v: Vec(A)(n)): Nat.zero = Nat.succ(Nat.zero) {
           |  by cases v { case vnil => trivial  case vcons m h t => trivial }
           |}
           |""".stripMargin,
      "absurd.sroof",
    )
    assert(r.isLeft, s"`zero = succ zero` must be rejected, got: $r")

  test("a concrete index is left alone rather than unified"):
    // `v : Vec A zero` gives the branches nothing to substitute — refining needs a
    // variable. Deciding `vnil` is the only reachable branch would need real
    // unification, so the goal stays unrefined and the proof fails. A false
    // negative, deliberately: the alternative is guessing inside the TCB.
    val r = Main.processSource(
      vec + vlenDef +
        """|defspec concrete(A: Type, v: Vec(A)(Nat.zero)): vlen(A, Nat.zero, v) = Nat.zero {
           |  by cases v { case vnil => trivial  case vcons m h t => trivial }
           |}
           |""".stripMargin,
      "concrete.sroof",
    )
    assert(r.isLeft, s"expected the documented false negative, got: $r")

  test("an indexed family may be used as a parameter type"):
    // `Bidirectional.infer` folded `Ind` over parameters only, so `Vec(A)(n)` in a
    // binder position failed with "Expected function type, got Type" — a theorem
    // could state an index but no definition could take one.
    // The proposition must be kernel-checked for this to mean anything: a `def`
    // body is not, so `vlenDef` alone would pass on any tree. A defspec's
    // parameters become Pi binders in a proposition the kernel does check.
    val r = Main.processSource(
      vec +
        """|defspec binder_ok(A: Type, n: Nat, v: Vec(A)(n)): n = n { by trivial }
           |""".stripMargin,
      "binder.sroof",
    )
    assert(r.isRight, s"`v: Vec(A)(n)` must be a legal parameter type, got: $r")

  // ---- backward compatibility ----

  test("a family whose constructors omit their indices is unchanged"):
    // This is the shape every pre-v0.10 declaration has, `stdlib/Vec.sroof`
    // included: `indices` is populated but no constructor states a return index,
    // so there is nothing to derive and the index stays phantom. It must keep
    // type-checking exactly as it did — including accepting the "wrong" length,
    // because that declaration never claimed one.
    val phantom =
      """|inductive Nat { case zero: Nat  case succ(n: Nat): Nat }
         |inductive PVec(A: Type)(n: Nat) {
         |  case pnil: PVec
         |  case pcons(head: A, tail: PVec(A)): PVec
         |}
         |defspec t: PVec(Nat)(Nat.succ(Nat.zero)) { PVec.pnil }
         |""".stripMargin
    val result = Main.processSource(phantom, "phantom.sroof")
    assert(
      result.isRight,
      s"a phantom-index declaration must behave as it did before v0.10, got: $result",
    )
