package sroof.annotation

import scala.annotation.StaticAnnotation

/** Marks an `object` whose contents are verified by the sroof compiler plugin.
 *
 *  Everything declared inside is treated as verified code: enums become
 *  inductive types, `def`s become core definitions, and `@theorem` methods are
 *  proved and re-checked by `sroof.kernel.Kernel.verify`.
 *
 *  The annotation on its own performs no verification.  It is inert unless the
 *  sroof compiler plugin is enabled for the compilation (`-Xplugin:...`).
 */
final class proofModule extends StaticAnnotation

/** Marks a method as a theorem to be proved at compile time.
 *
 *  The method must live inside a [[proofModule]], return exactly
 *  `sroof.lang.Proof`, and have a body of the form `prove(goal)(tactic)`.
 */
final class theorem extends StaticAnnotation

/** Marks a verified theorem as a default simplification lemma.
 *
 *  The theorem is added to `GlobalEnv.simpSet` only after the kernel accepts
 *  its proof, so an unproved theorem can never influence later proofs.
 */
final class simp extends StaticAnnotation
