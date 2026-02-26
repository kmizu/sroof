package sproof.syntax

import parsley.Parsley
import parsley.Parsley.{pure, empty, atomic}
import parsley.combinator.{option, sepBy, sepBy1, choice}
import parsley.token.Lexer
import parsley.token.descriptions.*
import parsley.token.Basic
import parsley.expr.chain
import parsley.syntax.zipped.*
import parsley.character.digit

/** Parser for the sproof surface syntax, built with Parsley 5.0.0-M9.
  *
  * All recursive grammar nonterminals are defined as `lazy val` with forward
  * references wrapped in by-name positions or `LazyParsley` to avoid
  * Scala 3 lazy-val initialization deadlocks.
  */
object Parser:

  // ---- Lexer setup ----

  private val lexer = new Lexer(LexicalDesc.plain.copy(
    nameDesc = NameDesc.plain.copy(
      identifierStart = Basic(c => c.isLetter || c == '_'),
      identifierLetter = Basic(c => c.isLetterOrDigit || c == '_'),
    ),
    spaceDesc = SpaceDesc.plain.copy(
      lineCommentStart = "//",
      multiLineCommentStart = "/*",
      multiLineCommentEnd = "*/",
    ),
    symbolDesc = SymbolDesc.plain.copy(
      hardKeywords = Set(
        "inductive", "def", "defspec", "case", "match", "by", "program",
        "trivial", "triv", "assume", "apply", "simplify", "simp",
        "induction", "sorry", "fun", "Pi", "Type",
      ),
      hardOperators = Set("->", "=", "=>", ":", ",", "{", "}", "(", ")", "[", "]", "."),
    ),
  ))

  // ---- Token helpers ----

  private val identifier = lexer.lexeme.names.identifier
  private def keyword(kw: String) = lexer.lexeme.symbol(kw)
  private def op(o: String) = lexer.lexeme.symbol(o)
  private val ws = lexer.space.whiteSpace

  private def parens[A](p: => Parsley[A]): Parsley[A] =
    op("(") *> p <* op(")")

  private def braces[A](p: => Parsley[A]): Parsley[A] =
    op("{") *> p <* op("}")

  private def brackets[A](p: => Parsley[A]): Parsley[A] =
    op("[") *> p <* op("]")

  private def many[A](p: => Parsley[A]): Parsley[List[A]] = Parsley.many(p)
  private def some[A](p: => Parsley[A]): Parsley[List[A]] = Parsley.some(p)

  // Forward-reference wrapper: delays evaluation of `p` until parse time.
  // pure(()) succeeds immediately, then flatMap evaluates p lazily.
  private def fwd[A](p: => Parsley[A]): Parsley[A] =
    pure(()).flatMap(_ => p)

  // ---- Type parsing ----
  // Using fwd() to break circular lazy val initialization

  private lazy val typeExpr: Parsley[SType] =
    chain.right1[SType](atomicType)(op("->") #> ((l: SType, r: SType) => SType.STArrow(l, r)))

  private lazy val atomicType: Parsley[SType] = choice(
    piType,
    uniType,
    typeVarOrApp,
    parens(fwd(typeExpr)),
  )

  /** Pi(x: A, B) */
  private lazy val piType: Parsley[SType] =
    keyword("Pi") *> op("(") *> identifier.flatMap { name =>
      op(":") *> fwd(typeExpr).flatMap { dom =>
        op(",") *> fwd(typeExpr).flatMap { cod =>
          op(")") #> SType.STPi(name, dom, cod)
        }
      }
    }

  /** Type, Type0, Type1, ...
    * Since "Type" is a hard keyword, "Type0" is parsed as identifier "Type0".
    * We handle both: keyword "Type" alone and identifiers matching Type\d.
    */
  private lazy val uniType: Parsley[SType] = choice(
    // Type0, Type1, ... as identifiers (since Type is hard keyword, Type0 is a valid identifier)
    atomic(identifier.collect {
      case s if s.startsWith("Type") && s.drop(4).forall(_.isDigit) && s.length > 4 =>
        SType.STUni(s.drop(4).toInt)
    }),
    // Bare "Type" keyword
    keyword("Type") #> SType.STUni(0),
  )

  /** Simple type variable or type application: Nat, List(A) */
  private lazy val typeVarOrApp: Parsley[SType] =
    identifier.flatMap { name =>
      option(parens(fwd(typeExpr))).map {
        case Some(arg) => SType.STApp(SType.STVar(name), arg)
        case None      => SType.STVar(name)
      }
    }

  // ---- Expression parsing ----

  private lazy val expr: Parsley[SExpr] = choice(
    matchExpr,
    lamExpr,
    appOrVarOrCon,
  )

  /** match e { case ... => ... } */
  private lazy val matchExpr: Parsley[SExpr] =
    keyword("match") *> simpleExpr.flatMap { scrutinee =>
      braces(many(matchCase)).map { cases =>
        SExpr.SEMatch(scrutinee, cases)
      }
    }

  private lazy val matchCase: Parsley[SMatchCase] =
    keyword("case") *> matchPattern.flatMap { case (ctor, bindings) =>
      op("=>") *> fwd(expr).map { body =>
        SMatchCase(ctor, bindings, body)
      }
    }

  /** Match pattern: Nat.zero, Nat.succ(k) */
  private lazy val matchPattern: Parsley[(String, List[String])] =
    identifier.flatMap { first =>
      option(op(".") *> identifier).flatMap {
        case Some(ctorName) =>
          val fullName = s"$first.$ctorName"
          option(parens(sepBy(identifier, op(",")))).map { bindings =>
            (fullName, bindings.getOrElse(Nil))
          }
        case None =>
          option(parens(sepBy(identifier, op(",")))).map { bindings =>
            (first, bindings.getOrElse(Nil))
          }
      }
    }

  /** fun (x: A) => body */
  private lazy val lamExpr: Parsley[SExpr] =
    keyword("fun") *> some(paramDecl).flatMap { params =>
      op("=>") *> fwd(expr).map { body =>
        SExpr.SELam(params, body)
      }
    }

  /** Variable, constructor (Type.ctor), or function application */
  private lazy val appOrVarOrCon: Parsley[SExpr] =
    identifier.flatMap { first =>
      option(op(".") *> identifier).flatMap {
        case Some(ctorName) =>
          option(parens(sepBy(fwd(expr), op(",")))).map { argsOpt =>
            SExpr.SECon(first, ctorName, argsOpt.getOrElse(Nil))
          }
        case None =>
          option(parens(sepBy(fwd(expr), op(",")))).map {
            case Some(args) => SExpr.SEApp(SExpr.SEVar(first), args)
            case None       => SExpr.SEVar(first)
          }
      }
    }

  /** Simple expression (no match, for scrutinee position) */
  private lazy val simpleExpr: Parsley[SExpr] = appOrVarOrCon

  // ---- Parameter declarations ----

  private lazy val paramDecl: Parsley[SParam] =
    parens(identifier.flatMap { name =>
      op(":") *> fwd(typeExpr).map { tpe =>
        SParam(name, tpe)
      }
    })

  private lazy val paramList: Parsley[List[SParam]] =
    parens(sepBy(
      identifier.flatMap { name =>
        op(":") *> fwd(typeExpr).map { tpe =>
          SParam(name, tpe)
        }
      },
      op(","),
    ))

  // ---- Declaration parsing ----

  private lazy val decl: Parsley[SDecl] = choice(
    inductiveDecl,
    defspecDecl,
    defDecl,
  )

  /** inductive Name(params) { case ctor1: T case ctor2(a: A): T } */
  private lazy val inductiveDecl: Parsley[SDecl] =
    keyword("inductive") *> identifier.flatMap { name =>
      option(paramList).map(_.getOrElse(Nil)).flatMap { params =>
        braces(many(ctorDecl)).map { ctors =>
          SDecl.SInductive(name, params, ctors)
        }
      }
    }

  private lazy val ctorDecl: Parsley[SCtor] =
    keyword("case") *> identifier.flatMap { name =>
      option(parens(sepBy(
        identifier.flatMap { pn =>
          op(":") *> fwd(typeExpr).map { pt =>
            SParam(pn, pt)
          }
        },
        op(","),
      ))).map(_.getOrElse(Nil)).flatMap { argParams =>
        op(":") *> fwd(typeExpr).map { retTpe =>
          SCtor(name, argParams, retTpe)
        }
      }
    }

  /** def name(params): retTpe = body  OR  def name(params): retTpe { body } */
  private lazy val defDecl: Parsley[SDecl] =
    keyword("def") *> identifier.flatMap { name =>
      paramList.flatMap { params =>
        (op(":") *> fwd(typeExpr)).flatMap { retTpe =>
          defBody.map { body =>
            SDecl.SDef(name, params, retTpe, body)
          }
        }
      }
    }

  private lazy val defBody: Parsley[SExpr] = choice(
    op("=") *> fwd(expr),
    braces(fwd(expr)),
  )

  /** defspec name(params): prop program = { by tactic } */
  private lazy val defspecDecl: Parsley[SDecl] =
    keyword("defspec") *> identifier.flatMap { name =>
      paramList.flatMap { params =>
        (op(":") *> propType).flatMap { prop =>
          (keyword("program") *> op("=") *> braces(proof)).map { prf =>
            SDecl.SDefspec(name, params, prop, prf)
          }
        }
      }
    }

  /** Proposition type: either an equality `expr = expr` or a regular type.
    * For equality, both sides are parsed as expressions (to allow `plus(n, Nat.zero) = n`).
    */
  private lazy val propType: Parsley[SType] = choice(
    // Try equality: expr = expr (must use atomic because expr might partially consume)
    atomic(fwd(expr).flatMap { lhs =>
      op("=") *> fwd(expr).map { rhs =>
        SType.STEq(lhs, rhs)
      }
    }),
    // Fallback: regular type
    fwd(typeExpr),
  )

  /** Proof: by tactic | direct expr */
  private lazy val proof: Parsley[SProof] = choice(
    keyword("by") *> tactic.map(SProof.SBy.apply),
    fwd(expr).map(SProof.STerm.apply),
  )

  // ---- Tactic parsing ----

  private lazy val tactic: Parsley[STactic] = choice(
    keyword("trivial") #> STactic.STrivial,
    keyword("triv") #> STactic.STriv,
    keyword("sorry") #> STactic.SSorry,
    keyword("assume") *> some(identifier).map(STactic.SAssume.apply),
    keyword("apply") *> fwd(expr).map(STactic.SApply.apply),
    keyword("simplify") *> brackets(sepBy(identifier, op(","))).map(STactic.SSimplify.apply),
    atomic(keyword("simp") *> brackets(sepBy(identifier, op(",")))).map(STactic.SSimp.apply),
    keyword("simp") #> STactic.SSimp(Nil),
    inductionTactic,
  )

  private lazy val inductionTactic: Parsley[STactic] =
    keyword("induction") *> identifier.flatMap { varName =>
      braces(many(tacticCase)).map { cases =>
        STactic.SInduction(varName, cases)
      }
    }

  private lazy val tacticCase: Parsley[STacticCase] =
    keyword("case") *> identifier.flatMap { ctorName =>
      many(atomic(identifier.filter(n => !isKeyword(n) && n != "=>"))).flatMap { bindings =>
        op("=>") *> tactic.map { tac =>
          STacticCase(ctorName, bindings, tac)
        }
      }
    }

  private val keywords = Set(
    "inductive", "def", "defspec", "case", "match", "by", "program",
    "trivial", "triv", "assume", "apply", "simplify", "simp",
    "induction", "sorry", "fun", "Pi", "Type",
  )

  private def isKeyword(s: String): Boolean = keywords.contains(s)

  // ---- Program (multiple decls) ----

  private lazy val program: Parsley[List[SDecl]] =
    ws *> many(decl) <* Parsley.eof

  // ---- Public API ----

  def parseType(input: String): Either[String, SType] =
    runParser(ws *> typeExpr <* Parsley.eof, input)

  def parseExpr(input: String): Either[String, SExpr] =
    runParser(ws *> expr <* Parsley.eof, input)

  def parseDecl(input: String): Either[String, SDecl] =
    runParser(ws *> decl <* Parsley.eof, input)

  def parseTactic(input: String): Either[String, STactic] =
    runParser(ws *> tactic <* Parsley.eof, input)

  def parseProgram(input: String): Either[String, List[SDecl]] =
    runParser(program, input)

  private def runParser[A](p: Parsley[A], input: String): Either[String, A] =
    p.parse(input) match
      case parsley.Success(value) => Right(value)
      case parsley.Failure(err)   => Left(err.toString)

end Parser
