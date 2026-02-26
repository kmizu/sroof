package sproof.checker

import sproof.core.{Term, Context}

/** Type errors produced by the bidirectional type checker. */
enum TypeError extends Exception:
  case UnboundVariable(idx: Int, ctx: Context)
  case TypeMismatch(expected: Term, actual: Term, term: Term, ctx: Context)
  case NotAFunction(term: Term, tpe: Term, ctx: Context)
  case UniverseOverflow(level: Int)
  case UnresolvedMeta(id: Int)
  case NotAType(term: Term, ctx: Context)
  case Custom(msg: String)

  override def getMessage: String = this match
    case UnboundVariable(i, _)      => s"Unbound variable at index $i"
    case TypeMismatch(exp, act, t, _) =>
      s"Type mismatch:\n  expected: ${exp.show}\n  actual:   ${act.show}\n  term:     ${t.show}"
    case NotAFunction(t, tp, _)     => s"Expected function type, got ${tp.show} for ${t.show}"
    case UniverseOverflow(l)        => s"Universe level $l is too large (max 100)"
    case UnresolvedMeta(i)          => s"Unresolved meta variable ?$i"
    case NotAType(t, _)             => s"Expected a type expression, got ${t.show}"
    case Custom(msg)                => msg
