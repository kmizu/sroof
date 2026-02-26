package sproof.tactic

import sproof.checker.TypeError

/** Errors that can arise during tactic execution. */
enum TacticError(msg: String) extends Exception(msg):
  case NoGoals
    extends TacticError("No goals remaining")

  case GoalMismatch(expected: String, got: String)
    extends TacticError(s"Goal mismatch: expected $expected, got $got")

  case NotAnEquality(goalStr: String)
    extends TacticError(s"Goal is not a propositional equality: $goalStr")

  case NotAFunction(termStr: String)
    extends TacticError(s"Term is not a function: $termStr")

  case NotAPi(goalStr: String)
    extends TacticError(s"Goal is not a Pi type (cannot introduce): $goalStr")

  case TypeCheckFailed(err: TypeError)
    extends TacticError(s"Type check failed: ${err.getMessage}")

  case Custom(message: String)
    extends TacticError(message)
