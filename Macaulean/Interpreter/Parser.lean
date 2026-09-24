import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Lexer

/-!
# Parser

A Pratt parser following the precedence table in the Macaulay2 grammar
<https://github.com/Macaulay2/M2/wiki/Macaulay2-language-grammar>
(highest binding first):

| operators            | associativity | binding power |
|----------------------|---------------|---------------|
| `^`                  | left          | 50            |
| `*` `/` `//` `%`     | left          | 40            |
| prefix `-` `+`       |               | 35            |
| `+` `-`              | left          | 30            |
| `<` `<=` `>` `>=` `==` `!=` | right  | 20            |
| `=`                  | right         | 10            |

The operand of a prefix operator is parsed at binding power
`max minBP 35`, where `minBP` is the binding power of the context.  This
matches Macaulay2: `-7//3` is `-(7//3)`, but `2 * -7 // 2` is `(2 * -7) // 2`.

Newlines end a statement, except directly after an operator or inside
parentheses.  Like the lexer, the parser recurses on fuel, so it is total and
the kernel can run it.
-/

namespace Macaulean.M2

namespace Parser

/-- Binding power of prefix `-` and `+`. -/
def prefixBP : Nat := 35

/-- What an infix symbol builds, with its left and right binding powers. -/
inductive Infix where
  | bin (op : BinOp)
  | assign

/-- Infix symbols: `(kind, left binding power, right binding power)`. -/
def infixInfo : Sym → Option (Infix × Nat × Nat)
  | .caret => some (.bin .pow, 50, 51)
  | .star => some (.bin .mul, 40, 41)
  | .slash => some (.bin .div, 40, 41)
  | .slashslash => some (.bin .quot, 40, 41)
  | .percent => some (.bin .rem, 40, 41)
  | .plus => some (.bin .add, 30, 31)
  | .minus => some (.bin .sub, 30, 31)
  | .lt => some (.bin .lt, 20, 20)
  | .le => some (.bin .le, 20, 20)
  | .gt => some (.bin .gt, 20, 20)
  | .ge => some (.bin .ge, 20, 20)
  | .eqeq => some (.bin .eq, 20, 20)
  | .ne => some (.bin .ne, 20, 20)
  | .assign => some (.assign, 10, 10)
  | _ => none

def skipNewlines : List Token → List Token
  | .newline :: ts => skipNewlines ts
  | ts => ts

abbrev Result := Except String (Term × List Token)

def describe : List Token → String
  | [] => "end of input"
  | t :: _ => s!"{repr t}"

mutual

/-- Parse an expression whose operators all bind at least as tightly as `minBP`.
`obey` says whether a newline ends the expression. -/
def parseExpr : Nat → Nat → Bool → List Token → Result
  | 0, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, ts =>
    match skipNewlines ts with
    | .num n :: rest => parseLoop fuel minBP obey (.int n) rest
    | .ident x :: rest => parseLoop fuel minBP obey (.var x) rest
    | .sym .lparen :: rest =>
      match parseExpr fuel 0 false rest with
      | .ok (e, rest) =>
        match skipNewlines rest with
        | .sym .rparen :: rest => parseLoop fuel minBP obey e rest
        | rest => .error s!"expected ')' but found {describe rest}"
      | .error err => .error err
    | .sym .minus :: rest => parsePrefix fuel minBP obey .neg rest
    | .sym .plus :: rest => parsePrefix fuel minBP obey .pos rest
    | rest => .error s!"expected an expression but found {describe rest}"

/-- Parse the operand of a prefix operator, then continue with infix operators. -/
def parsePrefix : Nat → Nat → Bool → UnOp → List Token → Result
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, op, ts =>
    match parseExpr fuel (max minBP prefixBP) obey ts with
    | .ok (e, rest) => parseLoop fuel minBP obey (.unop op e) rest
    | .error err => .error err

/-- Having parsed `lhs`, absorb infix operators binding at least as tightly as `minBP`. -/
def parseLoop : Nat → Nat → Bool → Term → List Token → Result
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, lhs, ts =>
    let ts := if obey then ts else skipNewlines ts
    match ts with
    | .sym s :: rest =>
      match infixInfo s with
      | some (kind, lbp, rbp) =>
        if minBP ≤ lbp then
          match parseExpr fuel rbp obey rest with
          | .ok (rhs, rest) =>
            match kind, lhs with
            | .bin op, _ => parseLoop fuel minBP obey (.binop op lhs rhs) rest
            | .assign, .var x => parseLoop fuel minBP obey (.assign x rhs) rest
            | .assign, _ => .error "left side of '=' must be a variable"
          | .error err => .error err
        else .ok (lhs, ts)
      | none => .ok (lhs, ts)
    | _ => .ok (lhs, ts)

end

/-- Parse `statement* expression?`, where statements end in `;` or a newline.
Statements are combined with `Term.seq`; the empty program is `Term.empty`. -/
def parseStatements : Nat → List Token → Except String Term
  | 0, _ => .error "parser ran out of fuel"
  | fuel + 1, ts =>
    match skipNewlines ts with
    | [] => .ok .empty
    | ts =>
      match parseExpr fuel 0 true ts with
      | .error err => .error err
      | .ok (e, rest) =>
        let next : Except String (List Token) :=
          match rest with
          | [] => .ok []
          | .newline :: rest => .ok rest
          | .sym .semi :: rest => .ok rest
          | rest => .error s!"unexpected {describe rest}"
        match next with
        | .error err => .error err
        | .ok rest =>
          match parseStatements fuel rest with
          | .ok .empty => .ok e
          | .ok e' => .ok (.seq e e')
          | .error err => .error err

end Parser

/-- Enough fuel to parse a token list: each call to `parseExpr`, `parsePrefix`
or `parseLoop` either consumes a token or returns, so a small multiple of the
number of tokens suffices. -/
def Parser.fuel (ts : List Token) : Nat := 4 * ts.length + 4

/-- Parse Macaulay2 source into a `Term`. -/
def parse (s : String) : Except String Term := do
  let ts ← Lexer.lex s
  Parser.parseStatements (Parser.fuel ts) ts

end Macaulean.M2
