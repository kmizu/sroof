package sroof.lang

/** The sroof proof DSL: ordinary, type-correct Scala 3 that the sroof compiler
 *  plugin recognises **by resolved symbol**, never by spelling.
 *
 *  Everything here lives at the top level of a single file on purpose.  A
 *  top-level `opaque type` is only transparent to definitions in the same
 *  synthetic wrapper object (`sroof.lang.lang$package`), so the DSL bodies below
 *  must sit beside the type declarations to return `()`.
 *
 *  Runtime behaviour: every operation is inert.  `prove` takes both of its
 *  arguments by name and discards them, so no goal or tactic is ever evaluated
 *  at runtime.  There is no reflection and no runtime proof checking — proofs
 *  are decided during compilation or not at all.
 */

/** A proposition.  Built by [[===]]; consumed by [[prove]]. */
opaque type Prop = Unit

/** Evidence that a proposition holds.  The result type of a `@theorem` method. */
opaque type Proof = Unit

/** A proof script.  Built by [[trivial]], [[induction]], [[simplify]]. */
opaque type Tactic = Unit

/** The equality proposition `lhs = rhs`.
 *
 *  Both sides must be verified computations over supported inductive types.
 */
extension [A](lhs: A) infix def ===(rhs: A): Prop = ()

/** State a goal and the script that proves it.
 *
 *  Both arguments are by-name and are never evaluated: this call is a
 *  compile-time declaration, not a computation.
 */
def prove(goal: => Prop)(tactic: => Tactic): Proof = ()

/** Close a goal whose two sides are definitionally equal. */
def trivial: Tactic = ()

/** Structural induction over `value`, which must be a parameter or pattern
 *  binder of a supported inductive type.
 *
 *  Every constructor must be covered exactly once, with no guards and no
 *  pattern alternatives.
 */
def induction[A](value: A)(cases: PartialFunction[A, Tactic]): Tactic = ()

/** The induction hypothesis for `value`.
 *
 *  Legal only inside a recursive branch of the enclosing [[induction]], applied
 *  to that branch's recursive field binder.
 */
def ih[A](value: A): Proof = ()

/** Rewrite the goal with the given lemmas, then close it. */
def simplify(lemmas: Proof*): Tactic = ()
