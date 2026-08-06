package sroof.examples.scala3

import munit.FunSuite
import NatProofs.*
import NatProofs.Nat.*

/** The verified module is still an ordinary Scala program.
 *
 *  `plus` is the real function the theorems are about — it is not regenerated
 *  from sroof core, and adding proofs does not change what it computes.  If
 *  verification ever started rewriting user code, this suite would notice.
 */
class NatProofsRuntimeSuite extends FunSuite:

  private def encode(n: Int): Nat =
    if n == 0 then Zero else Succ(encode(n - 1))

  private def decode(n: Nat): Int = n match
    case Zero    => 0
    case Succ(k) => 1 + decode(k)

  test("plus still computes at runtime") {
    assertEquals(decode(plus(encode(2), encode(3))), 5)
    assertEquals(decode(plus(Zero, encode(4))), 4)
    assertEquals(decode(plus(encode(4), Zero)), 4)
  }

  test("the theorems' own statements hold on concrete values") {
    for
      a <- 0 to 4
      b <- 0 to 4
    do assertEquals(decode(plus(encode(a), encode(b))), a + b, s"plus($a, $b)")
  }

  test("proof values are inert at runtime") {
    // Calling a theorem must not run a proof or throw; it is an erased marker.
    plusZeroRight(encode(3))
    refl(encode(2))
  }
