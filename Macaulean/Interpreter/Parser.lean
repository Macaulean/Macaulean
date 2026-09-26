import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Lexer

/-!
# Shared, total Pratt grammar

Both source-string evaluation and the native Lean syntax category use this
concrete tree parser. Binding powers retain the existing arithmetic table;
comparisons > not > and > or > assignment. Conditional predicates ignore
newlines, whereas branches obey the surrounding input context, as in M2's
`unaryif`. Semicolons inside parentheses form right-associated blocks.
-/

namespace Macaulean.M2
namespace Parser

def prefixBP : Nat := 35
def notBP : Nat := 19
/-- Conditional arms include assignment but not an unparenthesized semicolon. -/
def branchBP : Nat := 10

inductive Infix where
  | bin (op : BinOp)
  | logic (op : LogicOp)
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
  | .kwAnd => some (.logic .andOp, 18, 18)
  | .kwOr => some (.logic .orOp, 16, 16)
  | .assign => some (.assign, 10, 10)
  | _ => none

/-- All positions are indices into the original token stream, including newlines. -/
inductive Tree where
  | num (pos : Nat) (n : Nat)
  | var (pos : Nat) (name : String)
  | paren (left right : Nat) (body : Tree)
  | unop (pos : Nat) (op : UnOp) (arg : Tree)
  | binop (pos : Nat) (op : BinOp) (lhs rhs : Tree)
  | logic (pos : Nat) (op : LogicOp) (lhs rhs : Tree)
  | assign (pos : Nat) (name : String) (lhs rhs : Tree)
  | ifThen (ifPos thenPos : Nat) (condition yes : Tree)
  | ifElse (ifPos thenPos elsePos : Nat) (condition yes no : Tree)
  | seq (semiPos : Nat) (lhs rhs : Tree)
  | discard (semiPos : Nat) (lhs : Tree)
  deriving Repr, DecidableEq, Inhabited

def Tree.toTerm : Tree → Term
  | .num _ n => .int n
  | .var _ x => .var x
  | .paren _ _ t => t.toTerm
  | .unop _ op a => .unop op a.toTerm
  | .binop _ op a b => .binop op a.toTerm b.toTerm
  | .logic _ op a b => .logic op a.toTerm b.toTerm
  | .assign _ x _ b => .assign x b.toTerm
  | .ifThen _ _ c y => .ifThen c.toTerm y.toTerm
  | .ifElse _ _ _ c y n => .ifElse c.toTerm y.toTerm n.toTerm
  | .seq _ a b => .seq a.toTerm b.toTerm
  | .discard _ a => .seq a.toTerm .empty

def Tree.bounds : Tree → Nat × Nat
  | .num i _ | .var i _ => (i, i)
  | .paren i j _ => (i, j)
  | .unop i _ a => (i, a.bounds.2)
  | .binop _ _ a b | .logic _ _ a b | .assign _ _ a b | .seq _ a b =>
    (a.bounds.1, b.bounds.2)
  | .ifThen i _ _ y => (i, y.bounds.2)
  | .ifElse i _ _ _ _ n => (i, n.bounds.2)
  | .discard j a => (a.bounds.1, j)

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
    | .sym .lparen :: rest => do
      let (e, tail) ← parseTreeBlock fuel ⟨rest, c.index + 1⟩
      let tail := tail.skipNewlines
      match tail.tokens with
      | .sym .rparen :: rest =>
        parseTreeLoop fuel minBP obey (.paren c.index tail.index e) ⟨rest, tail.index + 1⟩
      | rest => .error s!"expected ')' but found {describe rest}"
    | .sym .minus :: rest =>
      parseTreePrefix fuel minBP obey c.index .neg ⟨rest, c.index + 1⟩
    | .sym .plus :: rest =>
      parseTreePrefix fuel minBP obey c.index .pos ⟨rest, c.index + 1⟩
    | .sym .kwNot :: rest =>
      parseTreePrefix fuel minBP obey c.index .notOp ⟨rest, c.index + 1⟩
    | .sym .kwIf :: rest =>
      parseTreeIf fuel minBP obey c.index ⟨rest, c.index + 1⟩
    | rest => .error s!"expected an expression but found {describe rest}"

def parseTreePrefix : Nat → Nat → Bool → Nat → UnOp → Cursor → TreeResult
  | 0, _, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, pos, op, c => do
    let bp := if op = .notOp then notBP else prefixBP
    let (e, tail) ← parseTreeExpr fuel (max minBP bp) obey c
    parseTreeLoop fuel minBP obey (.unop pos op e) tail

/-- Nearest-if attachment follows directly from recursive parsing of each arm. -/
def parseTreeIf : Nat → Nat → Bool → Nat → Cursor → TreeResult
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, ifPos, c => do
    let (condition, tail) ← parseTreeExpr fuel branchBP false c
    let tail := tail.skipNewlines
    match tail.tokens with
    | .sym .kwThen :: rest =>
      let thenPos := tail.index
      let (yes, tail) ← parseTreeExpr fuel branchBP obey ⟨rest, thenPos + 1⟩
      let tail := if obey then tail else tail.skipNewlines
      match tail.tokens with
      | .sym .kwElse :: rest =>
        let elsePos := tail.index
        let (no, tail) ← parseTreeExpr fuel branchBP obey ⟨rest, elsePos + 1⟩
        parseTreeLoop fuel minBP obey (.ifElse ifPos thenPos elsePos condition yes no) tail
      | _ => parseTreeLoop fuel minBP obey (.ifThen ifPos thenPos condition yes) tail
    | rest => .error s!"expected 'then' but found {describe rest}"

/-- Parenthesized blocks use semicolons, not newlines, to sequence statements.
A trailing semicolon evaluates the prefix but returns null, unlike top-level `value`.
Empty `()` is an M2 Sequence, not a scalar block, and is deliberately rejected. -/
def parseTreeBlock : Nat → Cursor → TreeResult
  | 0, _ => .error "parser ran out of fuel"
  | fuel + 1, c => do
    let (lhs, tail) ← parseTreeExpr fuel 0 false c
    let tail := tail.skipNewlines
    match tail.tokens with
    | .sym .semi :: rest =>
      let semiPos := tail.index
      let next := (Cursor.mk rest (semiPos + 1)).skipNewlines
      match next.tokens with
      | .sym .rparen :: _ => return (.discard semiPos lhs, next)
      | _ =>
        let (rhs, tail) ← parseTreeBlock fuel next
        return (.seq semiPos lhs rhs, tail)
    | _ => return (lhs, tail)

def parseTreeLoop : Nat → Nat → Bool → Tree → Cursor → TreeResult
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, lhs, c =>
    let c := if obey then c else c.skipNewlines
    match c.tokens with
    | .sym s :: rest =>
      match infixInfo s with
      | some (kind, lbp, rbp) =>
        if minBP ≤ lbp then do
          let (rhs, tail) ← parseTreeExpr fuel rbp obey ⟨rest, c.index + 1⟩
          match kind, lhs.toTerm with
          | .bin op, _ => parseTreeLoop fuel minBP obey (.binop c.index op lhs rhs) tail
          | .logic op, _ => parseTreeLoop fuel minBP obey (.logic c.index op lhs rhs) tail
          | .assign, .var x => parseTreeLoop fuel minBP obey (.assign c.index x lhs rhs) tail
          | .assign, _ => .error "left side of '=' must be a variable"
        else .ok (lhs, c)
      | none => .ok (lhs, c)
    | _ => .ok (lhs, c)

end

def parseExpr (fuel minBP : Nat) (obey : Bool) (ts : List Token) : Result := do
  let (t, tail) ← parseTreeExpr fuel minBP obey ⟨ts, 0⟩
  return (t.toTerm, tail.tokens)

/-- Preserve the original `value` interface: a final top-level `;` returns its value. -/
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

/-- Every recursive branch consumes a token or decreases the available fuel. -/
def fuel (ts : List Token) : Nat := 8 * ts.length + 8

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
