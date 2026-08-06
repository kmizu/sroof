package sroof.examples.scala3

import sroof.annotation.*
import sroof.lang.*

/** The Scala 3 equivalent of `examples/nat.sroof`.
 *
 *  This is an ordinary Scala file: Scala's own parser and typer process it, and
 *  `Nat`/`plus` are the real program — nothing here is generated from sroof core.
 *  What the sroof compiler plugin adds is that the four `@theorem` methods are
 *  proved during compilation and re-checked by the trusted kernel.  If any of
 *  them stopped holding, this file would stop compiling.
 */
@proofModule
object NatProofs:

  enum Nat:
    case Zero
    case Succ(n: Nat)

  import Nat.*

  def plus(n: Nat, m: Nat): Nat =
    n match
      case Zero    => m
      case Succ(k) => Succ(plus(k, m))

  @theorem
  def plusZeroLeft(m: Nat): Proof =
    prove(plus(Zero, m) === m)(
      trivial
    )

  @theorem
  def plusSuccLeft(n: Nat, m: Nat): Proof =
    prove(plus(Succ(n), m) === Succ(plus(n, m)))(
      trivial
    )

  @theorem
  def refl(n: Nat): Proof =
    prove(n === n)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => trivial
      }
    )

  @simp
  @theorem
  def plusZeroRight(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )

  // `cases` splits on constructors without generating a hypothesis. Use it when
  // the proof does not need one — `ih` is not available inside it.
  @theorem
  def plusZeroLeftByCases(n: Nat): Proof =
    prove(plus(Zero, n) === n)(
      cases(n) {
        case Zero    => trivial
        case Succ(k) => trivial
      }
    )

  // Curried parameter lists are supported; they flatten to the same core type as
  // a single list would.
  @theorem
  def plusSuccLeftCurried(n: Nat)(m: Nat): Proof =
    prove(plus(Succ(n), m) === Succ(plus(n, m)))(
      trivial
    )

  // `plusZeroRight` is tagged `@simp`, so a bare `simplify()` can reach for it —
  // but only because the kernel already accepted its proof above.
  @theorem
  def plusZeroRightAgain(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      simplify()
    )

  // `alwaysZero` discards its accumulator and recurses with a changed one, so in
  // the `Succ` branch the goal is about `Succ(acc)` rather than `acc`.  A
  // hypothesis fixed at the original `acc` would not apply — hence
  // `inductionGeneralizing`, and `exactIh` to instantiate it.
  def alwaysZero(n: Nat, acc: Nat): Nat =
    n match
      case Zero    => Zero
      case Succ(k) => alwaysZero(k, Succ(acc))

  // `have` breaks a proof into steps: the intermediate claim is proved as a goal
  // in its own right, then cited by name in the continuation.
  @theorem
  def plusZeroRightInSteps(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      induction(n) {
        case Zero => trivial
        case Succ(k) =>
          have(plus(k, Zero) === k)(simplify(ih(k))) { step =>
            simplify(step)
          }
      }
    )

  @theorem
  def alwaysZeroIsZero(n: Nat, acc: Nat): Proof =
    prove(alwaysZero(n, acc) === Zero)(
      inductionGeneralizing(n, acc) {
        case Zero    => trivial
        case Succ(k) => exactIh(k)(Succ(acc))
      }
    )
