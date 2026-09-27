/-! # Abstract syntax for the pure Macaulay2 language -/
namespace Macaulean.M2
inductive BinOp where
  | add | sub | mul | div | quot | rem | pow
  | eq | ne | lt | le | gt | ge
  | range | rangeExclusive | index | hasIndex | concat | repeat | compose
  deriving Repr, DecidableEq, Inhabited
inductive UnOp where
  | neg | pos | notOp | length
  deriving Repr, DecidableEq, Inhabited
inductive LogicOp where
  | andOp | orOp
  deriving Repr, DecidableEq, Inhabited
inductive Parameters where
  | variadic (name : String)
  | fixed (names : List String)
  deriving Repr, DecidableEq, Inhabited
def Parameters.names : Parameters → List String
  | .variadic x => [x] | .fixed xs => xs
def Parameters.toM2String : Parameters → String
  | .variadic x => x | .fixed xs => "(" ++ ", ".intercalate xs ++ ")"
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
  | lambda (params : Parameters) (body : Term)
  | apply (fn arg : Term)
  | localAssign (name : String) (rhs : Term)
  | assignMany (declareLocal : Bool) (names : List String) (rhs : Term)
  | localSymbol (name : String)
  | returnTerm (value : Term)
  /-- Names inside brackets are quoted; their current values are not evaluated. -/
  | polyRing (base : Term) (names : List String)
  deriving Repr, Inhabited
mutual
def Term.decEq (a b : Term) : Decidable (a = b) := by
  cases a <;> cases b
  case int.int n m => exact decidable_of_iff (n = m) (by simp only [Term.int.injEq])
  case var.var x y => exact decidable_of_iff (x = y) (by simp only [Term.var.injEq])
  case unop.unop op a op' b =>
    haveI := Term.decEq a b
    exact decidable_of_iff (op = op' ∧ a = b) (by simp only [Term.unop.injEq])
  case binop.binop op a b op' a' b' =>
    haveI := Term.decEq a a'
    haveI := Term.decEq b b'
    exact decidable_of_iff (op = op' ∧ a = a' ∧ b = b') (by simp only [Term.binop.injEq])
  case logic.logic op a b op' a' b' =>
    haveI := Term.decEq a a'
    haveI := Term.decEq b b'
    exact decidable_of_iff (op = op' ∧ a = a' ∧ b = b') (by simp only [Term.logic.injEq])
  case ifThen.ifThen c y c' y' =>
    haveI := Term.decEq c c'
    haveI := Term.decEq y y'
    exact decidable_of_iff (c = c' ∧ y = y') (by simp only [Term.ifThen.injEq])
  case ifElse.ifElse c y n c' y' n' =>
    haveI := Term.decEq c c'
    haveI := Term.decEq y y'
    haveI := Term.decEq n n'
    exact decidable_of_iff (c = c' ∧ y = y' ∧ n = n') (by simp only [Term.ifElse.injEq])
  case assign.assign x e y e' =>
    haveI := Term.decEq e e'
    exact decidable_of_iff (x = y ∧ e = e') (by simp only [Term.assign.injEq])
  case indexAssign.indexAssign a i v a' i' v' =>
    haveI := Term.decEq a a'
    haveI := Term.decEq i i'
    haveI := Term.decEq v v'
    exact decidable_of_iff (a = a' ∧ i = i' ∧ v = v') (by simp only [Term.indexAssign.injEq])
  case seq.seq a b a' b' =>
    haveI := Term.decEq a a'
    haveI := Term.decEq b b'
    exact decidable_of_iff (a = a' ∧ b = b') (by simp only [Term.seq.injEq])
  case empty.empty => exact isTrue rfl
  case listLit.listLit xs ys =>
    haveI := Term.listDecEq xs ys
    exact decidable_of_iff (xs = ys) (by simp only [Term.listLit.injEq])
  case sequence.sequence xs ys =>
    haveI := Term.listDecEq xs ys
    exact decidable_of_iff (xs = ys) (by simp only [Term.sequence.injEq])
  case lambda.lambda p a q b =>
    haveI := Term.decEq a b
    exact decidable_of_iff (p = q ∧ a = b) (by simp only [Term.lambda.injEq])
  case apply.apply f a g b =>
    haveI := Term.decEq f g
    haveI := Term.decEq a b
    exact decidable_of_iff (f = g ∧ a = b) (by simp only [Term.apply.injEq])
  case localAssign.localAssign x a y b =>
    haveI := Term.decEq a b
    exact decidable_of_iff (x = y ∧ a = b) (by simp only [Term.localAssign.injEq])
  case assignMany.assignMany l xs a l' ys b =>
    haveI := Term.decEq a b
    exact decidable_of_iff (l = l' ∧ xs = ys ∧ a = b) (by simp only [Term.assignMany.injEq])
  case localSymbol.localSymbol x y =>
    exact decidable_of_iff (x = y) (by simp only [Term.localSymbol.injEq])
  case returnTerm.returnTerm a b =>
    haveI := Term.decEq a b
    exact decidable_of_iff (a = b) (by simp only [Term.returnTerm.injEq])
  case polyRing.polyRing a xs b ys =>
    haveI := Term.decEq a b
    exact decidable_of_iff (a = b ∧ xs = ys) (by simp only [Term.polyRing.injEq])
  all_goals exact isFalse (by intro h; cases h)
termination_by structural a

def Term.listDecEq (xs ys : List Term) : Decidable (xs = ys) := by
  cases xs with
  | nil => cases ys with
    | nil => exact isTrue rfl
    | cons b ys => exact isFalse (by intro h; cases h)
  | cons a xs => cases ys with
    | nil => exact isFalse (by intro h; cases h)
    | cons b ys =>
      haveI := Term.decEq a b
      haveI := Term.listDecEq xs ys
      exact decidable_of_iff (a = b ∧ xs = ys) (by simp only [List.cons.injEq])
termination_by structural xs
end
instance : DecidableEq Term := Term.decEq
namespace BinOp
def symbol : BinOp → String
  | add => "+" | sub => "-" | mul => "*" | div => "/" | quot => "//"
  | rem => "%" | pow => "^" | eq => "==" | ne => "!=" | lt => "<"
  | le => "<=" | gt => ">" | ge => ">=" | range => ".."
  | rangeExclusive => "..<" | index => "#" | hasIndex => "#?"
  | concat => "|" | .repeat => ":" | compose => "@@"
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

def Term.comma (extend : Bool) (a b : Term) : Term :=
  match extend, a with
  | true, .sequence xs => .sequence (xs ++ [b]) | _, _ => .sequence [a, b]
def Term.inBraces (commaBody : Bool) (a : Term) : Term :=
  match commaBody, a with
  | true, .sequence xs => .listLit xs | _, _ => .listLit [a]
def Term.variableNames : List Term → Option (List String)
  | [] => some []
  | .var x :: ts => (x :: ·) <$> Term.variableNames ts
  | _ => none
mutual
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
  | .sequence [.empty] => "(1:(null;))"
  | .sequence [a] => s!"(1:({a.toM2String}))"
  | .sequence xs => "(" ++ ", ".intercalate (Term.strings xs) ++ ")"
  | .lambda ps body => s!"({ps.toM2String} -> {body.toM2String})"
  | .apply f a => s!"({f.toM2String} ({a.toM2String}))"
  | .localAssign x a => s!"({x} := {a.toM2String})"
  | .assignMany isLocal xs a =>
    "((" ++ ", ".intercalate xs ++ ") " ++ (if isLocal then ":=" else "=") ++ " " ++ a.toM2String ++ ")"
  | .localSymbol x => s!"(local {x})"
  | .returnTerm .empty => "(return)"
  | .returnTerm a => s!"(return {a.toM2String})"
  | .polyRing a xs => "(" ++ a.toM2String ++ ")[" ++ ", ".intercalate xs ++ "]"
def Term.strings : List Term → List String
  | [] => [] | a :: xs => a.toM2String :: Term.strings xs
end
end Macaulean.M2
