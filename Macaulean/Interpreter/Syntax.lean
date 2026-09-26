/-!
# Abstract syntax for the scalar Macaulay2 language

Control flow has dedicated constructors: its operands are not eagerly evaluated
by ordinary binary dispatch. Parentheses disappear during parsing; blocks use
`seq`, with `empty` for the omitted final value of a block ending in `;`.
-/

namespace Macaulean.M2

inductive BinOp where
  | add | sub | mul | div | quot | rem | pow
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

inductive UnOp where
  | neg | pos | notOp
  deriving Repr, DecidableEq, Inhabited

/-- The Boolean short-circuit operators, not their function-valued overloads. -/
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
  | seq (s e : Term)
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
  | neg => "-" | pos => "+" | notOp => "not"

end UnOp

namespace LogicOp

def symbol : LogicOp → String
  | andOp => "and" | orOp => "or"

/-- The left Boolean value for which the right expression is skipped. -/
def shortCircuit : LogicOp → Bool
  | andOp => false | orOp => true

end LogicOp

/-- Print sourced terms with enough parentheses to preserve control flow and blocks. -/
def Term.toM2String : Term → String
  | .int n => if n < 0 then s!"({n})" else toString n
  | .var x => x
  | .unop op a => s!"({op.symbol} {a.toM2String})"
  | .binop op a b => s!"({a.toM2String} {op.symbol} {b.toM2String})"
  | .logic op a b => s!"({a.toM2String} {op.symbol} {b.toM2String})"
  | .ifThen c y => s!"(if {c.toM2String} then {y.toM2String})"
  | .ifElse c y n => s!"(if {c.toM2String} then {y.toM2String} else {n.toM2String})"
  | .assign x e => s!"({x} = {e.toM2String})"
  | .seq s .empty => s!"({s.toM2String};)"
  | .seq s e => s!"({s.toM2String}; {e.toM2String})"
  | .empty => ""

end Macaulean.M2
