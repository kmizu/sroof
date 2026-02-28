package sproof.core

/** Strict positivity checker for inductive type definitions.
 *
 *  An inductive type `T` is strictly positive iff `T` never appears in a
 *  negative position in any constructor argument type. A position is negative
 *  when it is on the left side of an odd number of arrows (Pi domains).
 *
 *  Without this check, non-positive types can encode self-application paradoxes
 *  (Girard's paradox), making the logic inconsistent.
 */
object PositivityChecker:

  /** Check that all constructors of the inductive type `indName` are strictly positive.
   *
   *  @return Right(()) if all constructors pass, Left(error message) otherwise.
   */
  def check(indName: String, ctors: List[CtorDef]): Either[String, Unit] =
    ctors.foldLeft[Either[String, Unit]](Right(())) { (acc, ctor) =>
      acc.flatMap { _ =>
        ctor.argTpes.foldLeft[Either[String, Unit]](Right(())) { (acc2, argTpe) =>
          acc2.flatMap(_ => checkPositive(indName, ctor.name, argTpe))
        }
      }
    }

  /** Check that `indName` occurs only in strictly positive positions within `tpe`.
   *
   *  Polarity tracks whether we're in a positive (true) or negative (false) position.
   *  - At the top level, polarity is positive.
   *  - In the domain of a Pi (left of arrow), polarity flips.
   *  - In the codomain of a Pi (right of arrow), polarity is preserved.
   */
  private def checkPositive(indName: String, ctorName: String, tpe: Term): Either[String, Unit] =
    checkPolarity(indName, ctorName, tpe, positive = true)

  private def checkPolarity(indName: String, ctorName: String, tpe: Term, positive: Boolean): Either[String, Unit] =
    tpe match
      case Term.Ind(name, _, _) if name == indName =>
        if positive then Right(())
        else Left(
          s"Strict positivity violation: '$indName' appears in a negative position " +
          s"in constructor '$ctorName'"
        )

      case Term.Pi(_, dom, cod) =>
        for
          _ <- checkPolarity(indName, ctorName, dom, !positive)
          _ <- checkPolarity(indName, ctorName, cod, positive)
        yield ()

      case Term.App(fn, arg) =>
        for
          _ <- checkPolarity(indName, ctorName, fn, positive)
          _ <- checkPolarity(indName, ctorName, arg, positive)
        yield ()

      case Term.Lam(_, tp, body) =>
        for
          _ <- checkPolarity(indName, ctorName, tp, positive)
          _ <- checkPolarity(indName, ctorName, body, positive)
        yield ()

      case Term.Let(_, tp, defn, body) =>
        for
          _ <- checkPolarity(indName, ctorName, tp, positive)
          _ <- checkPolarity(indName, ctorName, defn, positive)
          _ <- checkPolarity(indName, ctorName, body, positive)
        yield ()

      case Term.Con(_, _, args) =>
        args.foldLeft[Either[String, Unit]](Right(())) { (acc, arg) =>
          acc.flatMap(_ => checkPolarity(indName, ctorName, arg, positive))
        }

      case Term.Mat(s, cases, rt) =>
        for
          _ <- checkPolarity(indName, ctorName, s, positive)
          _ <- checkPolarity(indName, ctorName, rt, positive)
          _ <- cases.foldLeft[Either[String, Unit]](Right(())) { (acc, c) =>
            acc.flatMap(_ => checkPolarity(indName, ctorName, c.body, positive))
          }
        yield ()

      case Term.Fix(_, tp, body) =>
        for
          _ <- checkPolarity(indName, ctorName, tp, positive)
          _ <- checkPolarity(indName, ctorName, body, positive)
        yield ()

      // Var, Uni, Meta, Ind(other name) — no occurrence of indName
      case _ => Right(())
