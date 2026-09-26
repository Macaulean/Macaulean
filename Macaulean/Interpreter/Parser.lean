import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Lexer

/-!
# Parser

One fuel-recursive Pratt grammar serves both `run` and the scoped Lean DSL.
`Tree` retains parentheses and token indices for the editor; `Tree.toTerm`
erases only that presentation information. No Lean parser is imported here.

Binding powers (highest first): `^` 50, `* / // %` 40, prefix signs 35,
`+ -` 30, comparisons 20, assignment 10. Powers and arithmetic associate
left, comparisons and assignment right. A prefix operand is read at
`max minBP 35`, as required for `-7//3` versus `2 * -7 // 2`.
-/

namespace Macaulean.M2
namespace Parser

def prefixBP : Nat := 35

inductive Infix where
  | bin (op : BinOp)
  | assign

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

/-- Concrete syntax, with indices into the original token stream. -/
inductive Tree where
  | num (tokenIndex : Nat) (n : Nat)
  | var (tokenIndex : Nat) (name : String)
  | paren (left right : Nat) (body : Tree)
  | unop (tokenIndex : Nat) (op : UnOp) (arg : Tree)
  | binop (tokenIndex : Nat) (op : BinOp) (lhs rhs : Tree)
  | assign (tokenIndex : Nat) (name : String) (lhs rhs : Tree)
  deriving Repr, DecidableEq, Inhabited

/-- Forget source information, not M2 semantics. -/
def Tree.toTerm : Tree → Term
  | .num _ n => .int n
  | .var _ x => .var x
  | .paren _ _ t => t.toTerm
  | .unop _ op a => .unop op a.toTerm
  | .binop _ op a b => .binop op a.toTerm b.toTerm
  | .assign _ x _ b => .assign x b.toTerm

/-- Inclusive first/last token indices. -/
def Tree.bounds : Tree → Nat × Nat
  | .num i _ | .var i _ => (i, i)
  | .paren i j _ => (i, j)
  | .unop i _ a => (i, a.bounds.2)
  | .binop _ _ a b | .assign _ _ a b => (a.bounds.1, b.bounds.2)

structure Cursor where
  tokens : List Token
  index : Nat := 0
  deriving Inhabited

private def skipNewlinesAux : List Token → Nat → Cursor
  | .newline :: ts, i => skipNewlinesAux ts (i + 1)
  | ts, i => ⟨ts, i⟩

def Cursor.skipNewlines (c : Cursor) : Cursor :=
  skipNewlinesAux c.tokens c.index

def skipNewlines (ts : List Token) : List Token :=
  (Cursor.skipNewlines ⟨ts, 0⟩).tokens

def describe : List Token → String
  | [] => "end of input"
  | t :: _ => s!"{repr t}"

abbrev TreeResult := Except String (Tree × Cursor)
abbrev Result := Except String (Term × List Token)

mutual

def parseTreeExpr : Nat → Nat → Bool → Cursor → TreeResult
  | 0, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, c =>
    let c := c.skipNewlines
    match c.tokens with
    | .num n :: rest => parseTreeLoop fuel minBP obey (.num c.index n) ⟨rest, c.index + 1⟩
    | .ident x :: rest => parseTreeLoop fuel minBP obey (.var c.index x) ⟨rest, c.index + 1⟩
    | .sym .lparen :: rest =>
      match parseTreeExpr fuel 0 false ⟨rest, c.index + 1⟩ with
      | .error err => .error err
      | .ok (e, tail) =>
        let tail := tail.skipNewlines
        match tail.tokens with
        | .sym .rparen :: rest =>
          parseTreeLoop fuel minBP obey (.paren c.index tail.index e) ⟨rest, tail.index + 1⟩
        | rest => .error s!"expected ')' but found {describe rest}"
    | .sym .minus :: rest =>
      parseTreePrefix fuel minBP obey c.index .neg ⟨rest, c.index + 1⟩
    | .sym .plus :: rest =>
      parseTreePrefix fuel minBP obey c.index .pos ⟨rest, c.index + 1⟩
    | rest => .error s!"expected an expression but found {describe rest}"

def parseTreePrefix : Nat → Nat → Bool → Nat → UnOp → Cursor → TreeResult
  | 0, _, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, tokenIndex, op, c =>
    match parseTreeExpr fuel (max minBP prefixBP) obey c with
    | .ok (e, tail) => parseTreeLoop fuel minBP obey (.unop tokenIndex op e) tail
    | .error err => .error err

def parseTreeLoop : Nat → Nat → Bool → Tree → Cursor → TreeResult
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, lhs, c =>
    let c := if obey then c else c.skipNewlines
    match c.tokens with
    | .sym s :: rest =>
      match infixInfo s with
      | some (kind, lbp, rbp) =>
        if minBP ≤ lbp then
          match parseTreeExpr fuel rbp obey ⟨rest, c.index + 1⟩ with
          | .error err => .error err
          | .ok (rhs, tail) =>
            match kind, lhs.toTerm with
            | .bin op, _ => parseTreeLoop fuel minBP obey (.binop c.index op lhs rhs) tail
            | .assign, .var x => parseTreeLoop fuel minBP obey (.assign c.index x lhs rhs) tail
            | .assign, _ => .error "left side of '=' must be a variable"
        else .ok (lhs, c)
      | none => .ok (lhs, c)
    | _ => .ok (lhs, c)

end

/-- Compatibility entry point: the old string interface uses the same grammar. -/
def parseExpr (fuel minBP : Nat) (obey : Bool) (ts : List Token) : Result := do
  let (t, tail) ← parseTreeExpr fuel minBP obey ⟨ts, 0⟩
  return (t.toTerm, tail.tokens)

/-- Statements retain the `value` convention: a final semicolon returns the value. -/
def parseStatements : Nat → List Token → Except String Term
  | 0, _ => .error "parser ran out of fuel"
  | fuel + 1, ts =>
    match skipNewlines ts with
    | [] => .ok .empty
    | ts => do
      let (e, rest) ← parseExpr fuel 0 true ts
      let rest ← match rest with
        | [] => .ok []
        | .newline :: rest | .sym .semi :: rest => .ok rest
        | rest => .error s!"unexpected {describe rest}"
      let next ← parseStatements fuel rest
      return match next with
        | .empty => e
        | e' => .seq e e'

/-- Same generous fuel bound as the original parser. -/
def fuel (ts : List Token) : Nat := 4 * ts.length + 4

/-- Parse one already-delimited REPL expression, retaining source indices. -/
def parseInputTree (ts : List Token) : Except String Tree := do
  let (tree, rest) ← parseTreeExpr (fuel ts) 0 true ⟨ts, 0⟩
  match rest.skipNewlines.tokens with
  | [] => return tree
  | rest => .error s!"unexpected {describe rest}"

end Parser

def parse (s : String) : Except String Term := do
  let ts ← Lexer.lex s
  Parser.parseStatements (Parser.fuel ts) ts

end Macaulean.M2
