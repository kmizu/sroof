package sroof.eval

import sroof.core.{Term, GlobalEnv}
import munit.FunSuite

/** Tests for eta conversion in definitional equality.
 *
 *  Eta rule: f ≡ λx. f(x) when f : Π(x:A).B
 *
 *  This is important for proofs involving function extensionality and
 *  for usability (avoiding explicit eta-expansion in proof terms).
 */
class EtaSuite extends FunSuite:

  given GlobalEnv = GlobalEnv.empty

  test("eta: f ≡ λx. f(x) for variable f"):
    // f = Var(0), λx. f(x) = Lam("x", A, App(Var(1), Var(0)))
    // In env of size 1: Var(0) = f
    val f     = Term.Var(0)
    val etaF  = Term.Lam("x", Term.Uni(0), Term.App(Term.Var(1), Term.Var(0)))
    assert(
      Quote.convEqual(1, List(Semantic.freshVar(0)), f, etaF),
      "f should be equal to λx. f(x) by eta"
    )

  test("eta: λx. f(x) ≡ f for variable f (symmetric)"):
    val f     = Term.Var(0)
    val etaF  = Term.Lam("x", Term.Uni(0), Term.App(Term.Var(1), Term.Var(0)))
    assert(
      Quote.convEqual(1, List(Semantic.freshVar(0)), etaF, f),
      "λx. f(x) should be equal to f by eta (symmetric)"
    )

  test("eta does not equate structurally different lambdas"):
    // λx. x ≢ λx. Type0
    val id   = Term.Lam("x", Term.Uni(0), Term.Var(0))
    val konst = Term.Lam("x", Term.Uni(0), Term.Uni(0))
    assert(
      !Quote.convEqual(0, Nil, id, konst),
      "λx.x should not equal λx.Type0"
    )

  test("eta: identity function = id by eta"):
    // (λx. x) ≡ (λy. (λx.x)(y))
    val idFn  = Term.Lam("x", Term.Uni(0), Term.Var(0))
    val wrapped = Term.Lam("y", Term.Uni(0),
      Term.App(Term.Lam("x", Term.Uni(0), Term.Var(0)), Term.Var(0)))
    assert(
      Quote.convEqual(0, Nil, idFn, wrapped),
      "id should equal λy. id(y) by beta+eta"
    )
