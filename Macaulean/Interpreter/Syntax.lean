/-!
# Abstract syntax for a fragment of the Macaulay2 language

See <https://github.com/Macaulay2/M2/wiki/Macaulay2-language-grammar>.
Parentheses are not represented: they only affect parsing.
-/

namespace Macaulean.M2

/-- Binary operators supported by the interpreter. -/
inductive BinOp where
  | add | sub | mul | div | quot | rem | pow
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- Prefix operators supported by the interpreter. -/
inductive UnOp where
  | neg | pos
  deriving Repr, DecidableEq, Inhabited

/-- Macaulay2 expressions. -/
inductive Term where
  | int (n : Int)
  | var (x : String)
  | unop (op : UnOp) (a : Term)
  | binop (op : BinOp) (a b : Term)
  /-- `x = e` -/
  | assign (x : String) (e : Term)
  /-- `s; e` (or `s` followed by a newline and then `e`) -/
  | seq (s e : Term)
  /-- the empty program, which evaluates to `null` -/
  | empty
  deriving Repr, DecidableEq, Inhabited

namespace BinOp

def symbol : BinOp → String
  | add => "+" | sub => "-" | mul => "*" | div => "/" | quot => "//"
  | rem => "%" | pow => "^" | eq => "==" | ne => "!=" | lt => "<"
  | le => "<=" | gt => ">" | ge => ">="

end BinOp

namespace UnOp

def symbol : UnOp → String
  | neg => "-" | pos => "+"

end UnOp

/-- Print a term as Macaulay2 source, fully parenthesized. -/
def Term.toM2String : Term → String
  | .int n => if n < 0 then s!"({n})" else toString n
  | .var x => x
  | .unop op a => s!"({op.symbol}{a.toM2String})"
  | .binop op a b => s!"({a.toM2String} {op.symbol} {b.toM2String})"
  | .assign x e => s!"({x} = {e.toM2String})"
  | .seq s e => s!"{s.toM2String}; {e.toM2String}"
  | .empty => ""

end Macaulean.M2
