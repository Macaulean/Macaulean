/-!
# Abstract syntax for the pure Macaulay2 fragment

Collection elements are expressions evaluated left to right. Commas construct
sequences syntactically: a parenthesized sequence is one element, never spliced.
Blocks retain `seq` and `empty`; `()` is instead `sequence []`.
-/

namespace Macaulean.M2

inductive BinOp where
  | add | sub | mul | div | quot | rem | pow
  | eq | ne | lt | le | gt | ge
  | range | rangeExclusive | index | hasIndex | concat | repeat
  deriving Repr, DecidableEq, Inhabited

inductive UnOp where
  | neg | pos | notOp | length
  deriving Repr, DecidableEq, Inhabited

inductive LogicOp where
  | andOp | orOp
  deriving Repr, DecidableEq, Inhabited

inductive Term where
  | int (n : Int)
  | var (x : String)
  | unop (op : UnOp) (a : Term)
  | binop (op : BinOp) (a b : Term)
  | logic (op : LogicOp) (a b : Term)
  | ifThen (condition yes : Term)
  | ifElse (condition yes no : Term)
  | assign (x : String) (e : Term)
  | indexAssign (collection index value : Term)
  | seq (s e : Term)
  | empty
  | listLit (elements : List Term)
  | sequence (elements : List Term)
  deriving Repr, DecidableEq, Inhabited

namespace BinOp

def symbol : BinOp → String
  | add => "+" | sub => "-" | mul => "*" | div => "/" | quot => "//"
  | rem => "%" | pow => "^" | eq => "==" | ne => "!=" | lt => "<"
  | le => "<=" | gt => ">" | ge => ">=" | range => ".."
  | rangeExclusive => "..<" | index => "#" | hasIndex => "#?"
  | concat => "|" | repeat => ":"

end BinOp

namespace UnOp

def symbol : UnOp → String
  | neg => "-" | pos => "+" | notOp => "not" | length => "#"

end UnOp

namespace LogicOp

def symbol : LogicOp → String
  | andOp => "and" | orOp => "or"

def shortCircuit : LogicOp → Bool
  | andOp => false | orOp => true

end LogicOp

/-- Extend only a syntactically unparenthesized comma chain, never a sequence value. -/
def Term.comma (extend : Bool) (a b : Term) : Term :=
  match extend, a with
  | true, .sequence xs => .sequence (xs ++ [b])
  | _, _ => .sequence [a, b]

/-- Braces delimit expressions; a comma chain supplies the elements directly. -/
def Term.inBraces (commaBody : Bool) (a : Term) : Term :=
  match commaBody, a with
  | true, .sequence xs => .listLit xs
  | _, _ => .listLit [a]

mutual

/-- Print with explicit parentheses, preserving nested collections and control flow. -/
def Term.toM2String : Term → String
  | .int n => if n < 0 then s!"({n})" else toString n
  | .var x => x
  | .unop op a => s!"({op.symbol} {a.toM2String})"
  | .binop op a b => s!"({a.toM2String} {op.symbol} {b.toM2String})"
  | .logic op a b => s!"({a.toM2String} {op.symbol} {b.toM2String})"
  | .ifThen c y => s!"(if {c.toM2String} then {y.toM2String})"
  | .ifElse c y n => s!"(if {c.toM2String} then {y.toM2String} else {n.toM2String})"
  | .assign x e => s!"({x} = {e.toM2String})"
  | .indexAssign a i v => s!"({a.toM2String}#{i.toM2String} = {v.toM2String})"
  | .seq s .empty => s!"({s.toM2String};)"
  | .seq s e => s!"({s.toM2String}; {e.toM2String})"
  | .empty => ""
  | .listLit [] => "{}"
  | .listLit [.empty] => "{(null;)}"
  | .listLit xs => "{" ++ ", ".intercalate (Term.strings xs) ++ "}"
  | .sequence [] => "()"
  | .sequence [a] => s!"(1:({a.toM2String}))"
  | .sequence xs => "(" ++ ", ".intercalate (Term.strings xs) ++ ")"

def Term.strings : List Term → List String
  | [] => []
  | a :: xs => a.toM2String :: Term.strings xs

end

end Macaulean.M2
