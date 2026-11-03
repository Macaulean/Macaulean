/-!
# Lexer

The lexer (like the parser) is total: it recurses on a fuel parameter rather
than using `partial` or well-founded recursion, so the kernel can run it and
theorems can be stated about Macaulay2 *source strings*.
-/

namespace Macaulean.M2

/-- Operator and punctuation symbols. -/
inductive Sym where
  | plus | minus | star | slash | slashslash | percent | caret
  | eqeq | ne | lt | le | gt | ge | assign
  | lparen | rparen | semi
  deriving Repr, DecidableEq, Inhabited

inductive Token where
  | num (n : Nat)
  | ident (x : String)
  | sym (s : Sym)
  | newline
  deriving Repr, DecidableEq, Inhabited

namespace Lexer

/-- The value of `c` as a digit in base `base`, if it is one. -/
def digitVal (base : Nat) (c : Char) : Option Nat :=
  let d :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  match d with
  | some d => if d < base then some d else none
  | none => none

/-- Read digits in base `base`, returning the accumulated number and the rest. -/
def digits (base : Nat) (acc : Nat) : List Char → Nat × List Char
  | [] => (acc, [])
  | c :: cs =>
    match digitVal base c with
    | some d => digits base (base * acc + d) cs
    | none => (acc, c :: cs)

def isIdentStart (c : Char) : Bool := c.isAlpha

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '\'' || c == '$'

/-- Split off the longest prefix whose characters satisfy `p`. -/
def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    if p c then
      let (a, b) := span p cs
      (c :: a, b)
    else ([], c :: cs)

/-- Drop everything up to (but not including) the next newline. -/
def dropComment : List Char → List Char
  | [] => []
  | '\n' :: cs => '\n' :: cs
  | _ :: cs => dropComment cs

/-- Read an integer literal: decimal, or `0b`/`0o`/`0x` prefixed. -/
def number : List Char → Nat × List Char
  | '0' :: b :: c :: cs =>
    let base? := if b = 'b' ∨ b = 'B' then some 2
      else if b = 'o' ∨ b = 'O' then some 8
      else if b = 'x' ∨ b = 'X' then some 16
      else none
    match base? with
    | some base =>
      if (digitVal base c).isSome then digits base 0 (c :: cs)
      else digits 10 0 ('0' :: b :: c :: cs)
    | none => digits 10 0 ('0' :: b :: c :: cs)
  | cs => digits 10 0 cs

/-- Recognize an operator or punctuation symbol at the start of the input. -/
def symbol : List Char → Option (Sym × List Char)
  | '/' :: '/' :: cs => some (.slashslash, cs)
  | '=' :: '=' :: cs => some (.eqeq, cs)
  | '!' :: '=' :: cs => some (.ne, cs)
  | '<' :: '=' :: cs => some (.le, cs)
  | '>' :: '=' :: cs => some (.ge, cs)
  | '+' :: cs => some (.plus, cs)
  | '-' :: cs => some (.minus, cs)
  | '*' :: cs => some (.star, cs)
  | '/' :: cs => some (.slash, cs)
  | '%' :: cs => some (.percent, cs)
  | '^' :: cs => some (.caret, cs)
  | '<' :: cs => some (.lt, cs)
  | '>' :: cs => some (.gt, cs)
  | '=' :: cs => some (.assign, cs)
  | '(' :: cs => some (.lparen, cs)
  | ')' :: cs => some (.rparen, cs)
  | ';' :: cs => some (.semi, cs)
  | _ => none

/-- The lexer loop.  Each step consumes at least one character, so `fuel`
equal to the length of the input suffices. -/
def lexAux : Nat → List Char → Except String (List Token)
  | _, [] => .ok []
  | 0, _ => .error "lexer ran out of fuel"
  | fuel + 1, c :: cs =>
    if c = '\n' then (Token.newline :: ·) <$> lexAux fuel cs
    else if c = ' ' ∨ c = '\t' ∨ c = '\r' then lexAux fuel cs
    else if c = '-' ∧ cs.head? = some '-' then lexAux fuel (dropComment cs)
    else if c.isDigit then
      let (n, rest) := number (c :: cs)
      if rest.head?.any (fun d => d = '.' ∨ d = 'p' ∨ d = 'e' ∨ d = 'E') then
        .error "floating point literals are not supported"
      else (Token.num n :: ·) <$> lexAux fuel rest
    else if isIdentStart c then
      let (x, rest) := span isIdentChar cs
      (Token.ident (String.ofList (c :: x)) :: ·) <$> lexAux fuel rest
    else match symbol (c :: cs) with
      | some (s, rest) => (Token.sym s :: ·) <$> lexAux fuel rest
      | none => .error s!"unsupported character '{c}'"

/-- Tokenize Macaulay2 source. -/
def lex (s : String) : Except String (List Token) :=
  let cs := s.toList
  lexAux cs.length cs

end Lexer

end Macaulean.M2
