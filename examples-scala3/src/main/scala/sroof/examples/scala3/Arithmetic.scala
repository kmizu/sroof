package sroof.examples.scala3

import sroof.annotation.*
import sroof.lang.*

/** Elementary arithmetic, proved from the Peano axioms.
 *
 *  This is the "what does it look like in practice" example: familiar theorems,
 *  built up in the order a textbook would, each one leaning on the ones above it.
 *  Everything here is ordinary Scala — `plus` and `mult` are the real functions,
 *  and the compiler plugin proves the annotated statements about them.
 */
@proofModule
object Arithmetic:

  enum Nat:
    case Zero
    case Succ(n: Nat)

  import Nat.*

  def plus(n: Nat, m: Nat): Nat =
    n match
      case Zero    => m
      case Succ(k) => Succ(plus(k, m))

  def mult(n: Nat, m: Nat): Nat =
    n match
      case Zero    => Zero
      case Succ(k) => plus(m, mult(k, m))

  // ---- Addition: the two defining equations ----
  //
  // Both hold by computation alone: `plus` recurses on its first argument, so
  // these are exactly its two branches.

  @theorem
  def plusZeroLeft(m: Nat): Proof =
    prove(plus(Zero, m) === m)(trivial)

  @theorem
  def plusSuccLeft(n: Nat, m: Nat): Proof =
    prove(plus(Succ(n), m) === Succ(plus(n, m)))(trivial)

  // ---- Addition: the mirror equations ----
  //
  // These do *not* hold by computation: `plus(n, Zero)` is stuck while `n` is a
  // variable.  They need induction on the first argument.

  @simp
  @theorem
  def plusZeroRight(n: Nat): Proof =
    prove(plus(n, Zero) === n)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )

  @simp
  @theorem
  def plusSuccRight(n: Nat, m: Nat): Proof =
    prove(plus(n, Succ(m)) === Succ(plus(n, m)))(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )

  // ---- Associativity ----
  //
  // Induction on the leftmost operand: each step peels one `Succ` off it, and
  // the hypothesis closes the rest.

  @theorem
  def plusAssoc(a: Nat, b: Nat, c: Nat): Proof =
    prove(plus(plus(a, b), c) === plus(a, plus(b, c)))(
      induction(a) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )

  // ---- Multiplication ----

  @theorem
  def multZeroLeft(m: Nat): Proof =
    prove(mult(Zero, m) === Zero)(trivial)

  @theorem
  def multSuccLeft(n: Nat, m: Nat): Proof =
    prove(mult(Succ(n), m) === plus(m, mult(n, m)))(trivial)

  @theorem
  def multZeroRight(n: Nat): Proof =
    prove(mult(n, Zero) === Zero)(
      induction(n) {
        case Zero    => trivial
        case Succ(k) => simplify(ih(k))
      }
    )
