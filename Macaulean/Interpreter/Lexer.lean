/-! # Total lexer shared with the located M2 worksheet reader -/
namespace Macaulean.M2
inductive Sym where
  | plus | minus | star | slash | slashslash | percent | caret
  | eqeq | ne | lt | le | gt | ge | assign
  | lparen | rparen | lbrace | rbrace | semi | comma
  | dotdot | dotdotless | sharp | sharpQuestion | bar | colon
  | kwIf | kwThen | kwElse | kwAnd | kwOr | kwNot
  | arrow | localAssign | kwLocal | kwReturn | atat
  | lbracket | rbracket | underscore
  deriving Repr, DecidableEq, Inhabited
inductive Token where
  | num (n : Nat) | ident (x : String) | sym (s : Sym) | newline
  deriving Repr, DecidableEq, Inhabited
namespace Lexer
def digitVal (base : Nat) (c : Char) : Option Nat :=
  let d := if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none
  match d with | some d => if d < base then some d else none | none => none

def digits (base acc : Nat) : List Char → Nat × List Char
  | [] => (acc, [])
  | c :: cs => match digitVal base c with
    | some d => digits base (base * acc + d) cs | none => (acc, c :: cs)
def isIdentStart (c : Char) : Bool := c.isAlpha
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '\'' || c == '$'
def identifierToken : String → Token
  | "if" => .sym .kwIf | "then" => .sym .kwThen | "else" => .sym .kwElse
  | "and" => .sym .kwAnd | "or" => .sym .kwOr | "not" => .sym .kwNot
  | "local" => .sym .kwLocal | "return" => .sym .kwReturn
  | name => .ident name

def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs => if p c then
      let (a, b) := span p cs
      (c :: a, b)
    else ([], c :: cs)
def dropComment : List Char → List Char
  | [] => [] | '\n' :: cs => '\n' :: cs | _ :: cs => dropComment cs

def number : List Char → Nat × List Char
  | '0' :: b :: c :: cs =>
    let base? := if b = 'b' ∨ b = 'B' then some 2
      else if b = 'o' ∨ b = 'O' then some 8
      else if b = 'x' ∨ b = 'X' then some 16 else none
    match base? with
    | some base => if (digitVal base c).isSome then digits base 0 (c :: cs)
        else digits 10 0 ('0' :: b :: c :: cs)
    | none => digits 10 0 ('0' :: b :: c :: cs)
  | cs => digits 10 0 cs

def floatSuffix : List Char → Bool
  | '.' :: '.' :: _ => false
  | '.' :: _ | 'p' :: _ | 'e' :: _ | 'E' :: _ => true | _ => false

def symbol : List Char → Option (Sym × List Char)
  | '-' :: '>' :: cs => some (.arrow, cs)
  | ':' :: '=' :: cs => some (.localAssign, cs)
  | '@' :: '@' :: cs => some (.atat, cs)
  | '.' :: '.' :: '<' :: cs => some (.dotdotless, cs)
  | '.' :: '.' :: cs => some (.dotdot, cs)
  | '#' :: '?' :: cs => some (.sharpQuestion, cs)
  | '/' :: '/' :: cs => some (.slashslash, cs)
  | '=' :: '=' :: cs => some (.eqeq, cs) | '!' :: '=' :: cs => some (.ne, cs)
  | '<' :: '=' :: cs => some (.le, cs) | '>' :: '=' :: cs => some (.ge, cs)
  | '+' :: cs => some (.plus, cs) | '-' :: cs => some (.minus, cs)
  | '*' :: cs => some (.star, cs) | '/' :: cs => some (.slash, cs)
  | '%' :: cs => some (.percent, cs) | '^' :: cs => some (.caret, cs)
  | '<' :: cs => some (.lt, cs) | '>' :: cs => some (.gt, cs)
  | '=' :: cs => some (.assign, cs)
  | '(' :: cs => some (.lparen, cs) | ')' :: cs => some (.rparen, cs)
  | '{' :: cs => some (.lbrace, cs) | '}' :: cs => some (.rbrace, cs)
  | '[' :: cs => some (.lbracket, cs) | ']' :: cs => some (.rbracket, cs)
  | '_' :: cs => some (.underscore, cs)
  | ';' :: cs => some (.semi, cs) | ',' :: cs => some (.comma, cs)
  | '#' :: cs => some (.sharp, cs) | '|' :: cs => some (.bar, cs)
  | ':' :: cs => some (.colon, cs) | _ => none

def lexAux : Nat → List Char → Except String (List Token)
  | _, [] => .ok [] | 0, _ => .error "lexer ran out of fuel"
  | fuel + 1, c :: cs =>
    if c = '\n' then (Token.newline :: ·) <$> lexAux fuel cs
    else if c = ' ' ∨ c = '\t' ∨ c = '\r' then lexAux fuel cs
    else if c = '-' ∧ cs.head? = some '-' then lexAux fuel (dropComment cs)
    else if c.isDigit then
      let (n, rest) := number (c :: cs)
      if floatSuffix rest then .error "floating point literals are not supported"
      else (Token.num n :: ·) <$> lexAux fuel rest
    else if isIdentStart c then
      let (x, rest) := span isIdentChar cs
      (identifierToken (String.ofList (c :: x)) :: ·) <$> lexAux fuel rest
    else match symbol (c :: cs) with
      | some (s, rest) => (Token.sym s :: ·) <$> lexAux fuel rest
      | none => .error s!"unsupported character '{c}'"
def lex (s : String) : Except String (List Token) :=
  let cs := s.toList
  lexAux cs.length cs
end Lexer
end Macaulean.M2
