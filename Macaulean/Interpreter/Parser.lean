import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Lexer

/-! # Shared concrete-tree Pratt grammar

Application is right-associative (46), below powers/indexing (50) and composition
(48), above multiplication (40). Arrow and assignments share precedence 10.
Parameter parentheses are retained until arity is determined, never erased early.
-/
namespace Macaulean.M2
namespace Parser

def prefixBP : Nat := 35
def notBP : Nat := 19
def branchBP : Nat := 10
def commaBP : Nat := 5
def applicationBP : Nat := 46
inductive Infix where
  | bin (op : BinOp) | logic (op : LogicOp) | assign | comma | arrow | localAssign

def infixInfo : Sym → Option (Infix × Nat × Nat)
  | .caret => some (.bin .pow, 50, 51)
  | .sharp => some (.bin .index, 50, 51)
  | .sharpQuestion => some (.bin .hasIndex, 50, 51)
  | .atat => some (.bin .compose, 48, 49)
  | .star => some (.bin .mul, 40, 41) | .slash => some (.bin .div, 40, 41)
  | .slashslash => some (.bin .quot, 40, 41) | .percent => some (.bin .rem, 40, 41)
  | .plus => some (.bin .add, 30, 31) | .minus => some (.bin .sub, 30, 31)
  | .dotdot => some (.bin .range, 25, 26) | .dotdotless => some (.bin .rangeExclusive, 25, 26)
  | .bar => some (.bin .concat, 23, 24) | .colon => some (.bin .repeat, 22, 22)
  | .lt => some (.bin .lt, 20, 20) | .le => some (.bin .le, 20, 20)
  | .gt => some (.bin .gt, 20, 20) | .ge => some (.bin .ge, 20, 20)
  | .eqeq => some (.bin .eq, 20, 20) | .ne => some (.bin .ne, 20, 20)
  | .kwAnd => some (.logic .andOp, 18, 18) | .kwOr => some (.logic .orOp, 16, 16)
  | .assign => some (.assign, 10, 10) | .localAssign => some (.localAssign, 10, 10)
  | .arrow => some (.arrow, 10, 10) | .comma => some (.comma, 5, 6)
  | _ => none

inductive Tree where
  | num (pos : Nat) (n : Nat)
  | var (pos : Nat) (name : String)
  | paren (left right : Nat) (body : Tree)
  | listBody (left right : Nat) (body : Tree)
  | emptyList (left right : Nat)
  | emptySequence (left right : Nat)
  | missing (anchor : Nat)
  | comma (pos : Nat) (lhs rhs : Tree)
  | unop (pos : Nat) (op : UnOp) (arg : Tree)
  | binop (pos : Nat) (op : BinOp) (lhs rhs : Tree)
  | logic (pos : Nat) (op : LogicOp) (lhs rhs : Tree)
  | assign (pos : Nat) (name : String) (lhs rhs : Tree)
  | indexAssign (pos : Nat) (lhs rhs : Tree)
  | ifThen (ifPos thenPos : Nat) (condition yes : Tree)
  | ifElse (ifPos thenPos elsePos : Nat) (condition yes no : Tree)
  | seq (pos : Nat) (lhs rhs : Tree)
  | discard (pos : Nat) (lhs : Tree)
  | lambda (pos : Nat) (params : Parameters) (lhs body : Tree)
  | apply (fn arg : Tree)
  | localAssign (pos : Nat) (name : String) (lhs rhs : Tree)
  | assignMany (pos : Nat) (declareLocal : Bool) (names : List String) (lhs rhs : Tree)
  | localSymbol (pos : Nat) (name : String) (identifier : Tree)
  | returnTerm (pos : Nat) (body : Tree)
  deriving Repr, DecidableEq, Inhabited

def Tree.isComma : Tree → Bool | .comma .. => true | _ => false

def Tree.toTerm : Tree → Term
  | .num _ n => .int n | .var _ x => .var x
  | .paren _ _ t => t.toTerm
  | .listBody _ _ t => Term.inBraces t.isComma t.toTerm
  | .emptyList .. => .listLit [] | .emptySequence .. => .sequence [] | .missing _ => .empty
  | .comma _ a b => Term.comma a.isComma a.toTerm b.toTerm
  | .unop _ op a => .unop op a.toTerm
  | .binop _ op a b => .binop op a.toTerm b.toTerm
  | .logic _ op a b => .logic op a.toTerm b.toTerm
  | .assign _ x _ b => .assign x b.toTerm
  | .indexAssign _ a b => match a.toTerm with
    | .binop .index c i => .indexAssign c i b.toTerm | _ => .empty
  | .ifThen _ _ c y => .ifThen c.toTerm y.toTerm
  | .ifElse _ _ _ c y n => .ifElse c.toTerm y.toTerm n.toTerm
  | .seq _ a b => .seq a.toTerm b.toTerm | .discard _ a => .seq a.toTerm .empty
  | .lambda _ p _ b => .lambda p b.toTerm
  | .apply f a => .apply f.toTerm a.toTerm
  | .localAssign _ x _ a => .localAssign x a.toTerm
  | .assignMany _ loc xs _ a => .assignMany loc xs a.toTerm
  | .localSymbol _ x _ => .localSymbol x
  | .returnTerm _ a => .returnTerm a.toTerm

def Tree.bounds : Tree → Nat × Nat
  | .num i _ | .var i _ | .missing i => (i, i)
  | .paren i j _ | .listBody i j _ | .emptyList i j | .emptySequence i j => (i, j)
  | .unop i _ a | .returnTerm i a | .localSymbol i _ a => (i, a.bounds.2)
  | .binop _ _ a b | .logic _ _ a b | .assign _ _ a b
  | .seq _ a b | .comma _ a b | .indexAssign _ a b | .apply a b
  | .lambda _ _ a b | .localAssign _ _ a b | .assignMany _ _ _ a b => (a.bounds.1, b.bounds.2)
  | .ifThen i _ _ y => (i, y.bounds.2) | .ifElse i _ _ _ _ n => (i, n.bounds.2)
  | .discard i a => (a.bounds.1, i)

def Tree.parameterNames : Tree → Option (List String)
  | .var _ x => some [x]
  | .comma _ a (.var _ x) => (· ++ [x]) <$> a.parameterNames
  | _ => none

def Tree.parameters (t : Tree) : Except String Parameters := do
  let p : Parameters ← match t with
    | .var _ x => .ok (.variadic x)
    | .emptySequence .. => .ok (.fixed [])
    | .paren _ _ a => match a.parameterNames with
      | some xs => .ok (.fixed xs) | none => .error "expected a list of parameter names"
    | _ => .error "invalid function parameter syntax"
  if p.names.eraseDups.length != p.names.length then .error "duplicate function parameter"
  else return p

/-- Assignment targets are validated independently of expression/operator dispatch. -/
def assignmentTree (isLocal : Bool) (pos : Nat) (lhs rhs : Tree) : Except String Tree :=
  match lhs.toTerm with
  | .var name => .ok (if isLocal then .localAssign pos name lhs rhs else .assign pos name lhs rhs)
  | .sequence xs => do
    let some names := Term.variableNames xs | .error "expected variable names in multiple assignment"
    return .assignMany pos isLocal names lhs rhs
  | .binop .index _ _ =>
    if isLocal then .error "invalid local assignment target" else .ok (.indexAssign pos lhs rhs)
  | _ => .error "invalid assignment target"

structure Cursor where
  tokens : List Token
  index : Nat := 0
  deriving Inhabited
private def skipNewlinesAux : List Token → Nat → Cursor
  | .newline :: ts, i => skipNewlinesAux ts (i + 1) | ts, i => ⟨ts, i⟩
def Cursor.skipNewlines (c : Cursor) : Cursor := skipNewlinesAux c.tokens c.index
def skipNewlines (ts : List Token) : List Token := (Cursor.skipNewlines ⟨ts, 0⟩).tokens
def describe : List Token → String | [] => "end of input" | t :: _ => s!"{repr t}"
abbrev TreeResult := Except String (Tree × Cursor)
abbrev Result := Except String (Term × List Token)
private def missingOperand : List Token → Bool
  | [] | .newline :: _ | .sym .comma :: _ | .sym .semi :: _
  | .sym .rparen :: _ | .sym .rbrace :: _ | .sym .kwElse :: _ => true | _ => false
private def startsArgument : List Token → Bool
  | .num _ :: _ | .ident _ :: _ | .sym .lparen :: _ | .sym .lbrace :: _
  | .sym .kwIf :: _ | .sym .kwLocal :: _ | .sym .kwReturn :: _ | .sym .kwNot :: _ => true
  | _ => false

mutual

def parseTreeExpr : Nat → Nat → Bool → Cursor → TreeResult
  | 0, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, c =>
    let c := c.skipNewlines
    match c.tokens with
    | .num n :: rest => parseTreeLoop fuel minBP obey (.num c.index n) ⟨rest, c.index + 1⟩
    | .ident x :: rest => parseTreeLoop fuel minBP obey (.var c.index x) ⟨rest, c.index + 1⟩
    | .sym .lparen :: rest => parseDelimited fuel minBP obey false c.index ⟨rest, c.index + 1⟩
    | .sym .lbrace :: rest => parseDelimited fuel minBP obey true c.index ⟨rest, c.index + 1⟩
    | .sym .minus :: rest => parseTreePrefix fuel minBP obey c.index .neg ⟨rest, c.index + 1⟩
    | .sym .plus :: rest => parseTreePrefix fuel minBP obey c.index .pos ⟨rest, c.index + 1⟩
    | .sym .kwNot :: rest => parseTreePrefix fuel minBP obey c.index .notOp ⟨rest, c.index + 1⟩
    | .sym .sharp :: rest => parseTreePrefix fuel minBP obey c.index .length ⟨rest, c.index + 1⟩
    | .sym .kwIf :: rest => parseTreeIf fuel minBP obey c.index ⟨rest, c.index + 1⟩
    | .sym .kwLocal :: rest =>
      let next := (Cursor.mk rest (c.index + 1)).skipNewlines
      match next.tokens with
      | .ident x :: tail => parseTreeLoop fuel minBP obey
          (.localSymbol c.index x (.var next.index x)) ⟨tail, next.index + 1⟩
      | _ => .error "expected a name after 'local'"
    | .sym .kwReturn :: rest => do
      let next := Cursor.mk rest (c.index + 1)
      let next := if obey then next else next.skipNewlines
      let (a, tail) ← if missingOperand next.tokens then .ok (.missing c.index, next)
        else parseTreeExpr fuel branchBP obey next
      parseTreeLoop fuel minBP obey (.returnTerm c.index a) tail
    | .sym .comma :: _ =>
      if minBP ≤ commaBP then parseTreeLoop fuel minBP obey (.missing c.index) c
      else .error "unexpected comma in operand"
    | rest => .error s!"expected an expression but found {describe rest}"

def parseDelimited : Nat → Nat → Bool → Bool → Nat → Cursor → TreeResult
  | 0, _, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, braces, left, c => do
    let close := if braces then Sym.rbrace else Sym.rparen
    let c := c.skipNewlines
    match c.tokens with
    | .sym s :: rest =>
      if s = close then
        let t := if braces then Tree.emptyList left c.index else Tree.emptySequence left c.index
        return ← parseTreeLoop fuel minBP obey t ⟨rest, c.index + 1⟩
    | _ => pure ()
    let (body, tail) ← parseTreeBlock fuel close c
    let tail := tail.skipNewlines
    match tail.tokens with
    | .sym s :: rest =>
      if s = close then
        let t := if braces then Tree.listBody left tail.index body else Tree.paren left tail.index body
        parseTreeLoop fuel minBP obey t ⟨rest, tail.index + 1⟩
      else .error "mismatched collection or block delimiter"
    | rest => .error ((if braces then "expected '}' but found " else "expected ')' but found ") ++ describe rest)

def parseTreePrefix : Nat → Nat → Bool → Nat → UnOp → Cursor → TreeResult
  | 0, _, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, pos, op, c => do
    let bp := match op with | .notOp => notBP | .length => 45 | _ => prefixBP
    let (a, tail) ← parseTreeExpr fuel (max minBP bp) obey c
    parseTreeLoop fuel minBP obey (.unop pos op a) tail

def parseTreeIf : Nat → Nat → Bool → Nat → Cursor → TreeResult
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, pos, c => do
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
        parseTreeLoop fuel minBP obey (.ifElse pos thenPos elsePos condition yes no) tail
      | _ => parseTreeLoop fuel minBP obey (.ifThen pos thenPos condition yes) tail
    | _ => .error "expected 'then' to match 'if'"

def parseTreeBlock : Nat → Sym → Cursor → TreeResult
  | 0, _, _ => .error "parser ran out of fuel"
  | fuel + 1, close, c => do
    let (lhs, tail) ← parseTreeExpr fuel 0 false c
    let tail := tail.skipNewlines
    match tail.tokens with
    | .sym .semi :: rest =>
      let next := (Cursor.mk rest (tail.index + 1)).skipNewlines
      if next.tokens.head? = some (.sym close) then return (.discard tail.index lhs, next)
      let (rhs, next) ← parseTreeBlock fuel close next
      return (.seq tail.index lhs rhs, next)
    | _ => return (lhs, tail)

def parseCommaRhs : Nat → Bool → Nat → Cursor → TreeResult
  | 0, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, obey, anchor, c =>
    let c := if obey then c else c.skipNewlines
    if missingOperand c.tokens then .ok (.missing anchor, c)
    else parseTreeExpr fuel (commaBP + 1) obey c

def parseTreeLoop : Nat → Nat → Bool → Tree → Cursor → TreeResult
  | 0, _, _, _, _ => .error "parser ran out of fuel"
  | fuel + 1, minBP, obey, lhs, c =>
    let c := if obey then c else c.skipNewlines
    if startsArgument c.tokens && minBP ≤ applicationBP then do
      let (rhs, tail) ← parseTreeExpr fuel applicationBP obey c
      parseTreeLoop fuel minBP obey (.apply lhs rhs) tail
    else
      match c.tokens with
      | .sym s :: rest =>
        match infixInfo s with
        | some (kind, lbp, rbp) =>
          if minBP ≤ lbp then do
            let next := Cursor.mk rest (c.index + 1)
            match kind with
            | .comma =>
              let (rhs, tail) ← parseCommaRhs fuel obey c.index next
              parseTreeLoop fuel minBP obey (.comma c.index lhs rhs) tail
            | .arrow =>
              let params ← lhs.parameters
              let (rhs, tail) ← parseTreeExpr fuel rbp obey next
              parseTreeLoop fuel minBP obey (.lambda c.index params lhs rhs) tail
            | .assign =>
              let (rhs, tail) ← parseTreeExpr fuel rbp obey next
              let result ← assignmentTree false c.index lhs rhs
              parseTreeLoop fuel minBP obey result tail
            | .localAssign =>
              let (rhs, tail) ← parseTreeExpr fuel rbp obey next
              let result ← assignmentTree true c.index lhs rhs
              parseTreeLoop fuel minBP obey result tail
            | .bin op =>
              let (rhs, tail) ← parseTreeExpr fuel rbp obey next
              parseTreeLoop fuel minBP obey (.binop c.index op lhs rhs) tail
            | .logic op =>
              let (rhs, tail) ← parseTreeExpr fuel rbp obey next
              parseTreeLoop fuel minBP obey (.logic c.index op lhs rhs) tail
          else .ok (lhs, c)
        | none => .ok (lhs, c)
      | _ => .ok (lhs, c)
end

def parseExpr (fuel minBP : Nat) (obey : Bool) (ts : List Token) : Result := do
  let (t, tail) ← parseTreeExpr fuel minBP obey ⟨ts, 0⟩
  return (t.toTerm, tail.tokens)
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
      return match next with | .empty => e | e' => .seq e e'
def fuel (ts : List Token) : Nat := 16 * ts.length + 16

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
