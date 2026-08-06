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

  @theorem
  def plusZeroRight(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )
