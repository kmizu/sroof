package sproof.core

/** De Bruijn substitution and shifting operations.
 *
 *  - shift(d, t)       : lift all free variables in t by d levels
 *  - shiftFrom(c, d, t): lift free variables >= cutoff c by d levels
 *  - subst(s, t)       : substitute De Bruijn index 0 in t with s (one step of beta)
 *  - substN(s, j, t)   : substitute De Bruijn index j in t with s
 */
object Subst:

  /** Shift free variables at or above cutoff `c` by `d` in term `t`. */
  def shiftFrom(c: Int, d: Int, t: Term): Term = t match
    case Term.Var(i)           => if i >= c then Term.Var(i + d) else t
    case Term.App(f, a)        => Term.App(shiftFrom(c, d, f), shiftFrom(c, d, a))
    case Term.Lam(x, tp, b)   => Term.Lam(x, shiftFrom(c, d, tp), shiftFrom(c + 1, d, b))
    case Term.Pi(x, dm, cd)   => Term.Pi(x, shiftFrom(c, d, dm), shiftFrom(c + 1, d, cd))
    case Term.Let(x, tp, df, b) =>
      Term.Let(x, shiftFrom(c, d, tp), shiftFrom(c, d, df), shiftFrom(c + 1, d, b))
    case Term.Uni(_)           => t
    case Term.Ind(n, ps, cs)   =>
      Term.Ind(n,
        ps.map(p => Param(p.name, shiftFrom(c, d, p.tpe))),
        cs.map(ct => Ctor(ct.name, shiftFrom(c, d, ct.tpe))))
    case Term.Con(n, r, args)  => Term.Con(n, r, args.map(shiftFrom(c, d, _)))
    case Term.Mat(s, cases, rt) =>
      Term.Mat(
        shiftFrom(c, d, s),
        cases.map(mc => mc.copy(body = shiftFrom(c + mc.bindings, d, mc.body))),
        shiftFrom(c, d, rt),
      )
    case Term.Fix(n, tp, b)    => Term.Fix(n, shiftFrom(c, d, tp), shiftFrom(c + 1, d, b))
    case Term.Meta(_)          => t

  /** Shift all free variables in `t` by `d`. */
  def shift(d: Int, t: Term): Term = shiftFrom(0, d, t)

  /** Substitute De Bruijn index `j` in term `t` with `s`. */
  def substN(s: Term, j: Int, t: Term): Term = t match
    case Term.Var(i)           =>
      if i == j      then shift(j, s)
      else if i > j  then Term.Var(i - 1)
      else t
    case Term.App(f, a)        => Term.App(substN(s, j, f), substN(s, j, a))
    case Term.Lam(x, tp, b)   => Term.Lam(x, substN(s, j, tp), substN(s, j + 1, b))
    case Term.Pi(x, dm, cd)   => Term.Pi(x, substN(s, j, dm), substN(s, j + 1, cd))
    case Term.Let(x, tp, df, b) =>
      Term.Let(x, substN(s, j, tp), substN(s, j, df), substN(s, j + 1, b))
    case Term.Uni(_)           => t
    case Term.Ind(n, ps, cs)   =>
      Term.Ind(n,
        ps.map(p => Param(p.name, substN(s, j, p.tpe))),
        cs.map(ct => Ctor(ct.name, substN(s, j, ct.tpe))))
    case Term.Con(n, r, args)  => Term.Con(n, r, args.map(substN(s, j, _)))
    case Term.Mat(sc, cases, rt) =>
      Term.Mat(
        substN(s, j, sc),
        cases.map(mc => mc.copy(body = substN(s, j + mc.bindings, mc.body))),
        substN(s, j, rt),
      )
    case Term.Fix(n, tp, b)    => Term.Fix(n, substN(s, j, tp), substN(s, j + 1, b))
    case Term.Meta(_)          => t

  /** Substitute De Bruijn index 0 in `t` with `s` (beta-reduction step). */
  def subst(s: Term, t: Term): Term = substN(s, 0, t)

  /** Open a binder body by substituting a specific term for index 0. */
  def open(body: Term, v: Term): Term = subst(v, body)
