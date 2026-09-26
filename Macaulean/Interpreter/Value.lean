/-! # Immutable runtime values and structurally recursive equality -/
namespace Macaulean.M2

inductive Value where
  | zz (n : Int)
  | qq (q : Rat)
  | bool (b : Bool)
  | null
  | list (elements : List Value)
  | sequence (elements : List Value)
  deriving Repr, Inhabited

-- Nested inductives require explicit equality decisions. All recursive calls
-- descend through constructors; no native decision procedure is trusted.
mutual

def Value.decEq (a b : Value) : Decidable (a = b) := by
  cases a <;> cases b
  case zz.zz n m => exact decidable_of_iff (n = m) (by simp only [Value.zz.injEq])
  case qq.qq p q => exact decidable_of_iff (p = q) (by simp only [Value.qq.injEq])
  case bool.bool p q => exact decidable_of_iff (p = q) (by simp only [Value.bool.injEq])
  case null.null => exact isTrue rfl
  case list.list xs ys =>
    haveI := Value.listDecEq xs ys
    exact decidable_of_iff (xs = ys) (by simp only [Value.list.injEq])
  case sequence.sequence xs ys =>
    haveI := Value.listDecEq xs ys
    exact decidable_of_iff (xs = ys) (by simp only [Value.sequence.injEq])
  all_goals exact isFalse (by intro h; cases h)
termination_by structural a

def Value.listDecEq (xs ys : List Value) : Decidable (xs = ys) := by
  cases xs with
  | nil => cases ys with
    | nil => exact isTrue rfl
    | cons b ys => exact isFalse (by intro h; cases h)
  | cons a xs => cases ys with
    | nil => exact isFalse (by intro h; cases h)
    | cons b ys =>
      haveI := Value.decEq a b
      haveI := Value.listDecEq xs ys
      exact decidable_of_iff (a = b ∧ xs = ys) (by simp only [List.cons.injEq])
termination_by structural xs

end

instance : DecidableEq Value := Value.decEq

inductive Error where
  | divByZero
  | unboundVar (x : String)
  | protectedSymbol (x : String)
  | noMethod (op : String) (classes : List String)
  | conditionNotBoolean (actualClass : String)
  | indexOutOfBounds (index : Int) (length : Nat)
  | immutableCollection (actualClass : String)
  deriving DecidableEq, Repr, Inhabited

namespace Value

def className : Value → String
  | zz _ => "ZZ" | qq _ => "QQ" | bool _ => "Boolean" | null => "Nothing"
  | list _ => "List" | sequence _ => "Sequence"

mutual

def toM2String : Value → String
  | zz n => toString n
  | qq q => s!"{q.num}/{q.den}"
  | bool b => toString b
  | null => "null"
  | list xs => "{" ++ ", ".intercalate (strings xs) ++ "}"
  | sequence [] => "()"
  | sequence [v] => s!"1:({toM2String v})"
  | sequence xs => "(" ++ ", ".intercalate (strings xs) ++ ")"

def strings : List Value → List String
  | [] => []
  | v :: vs => toM2String v :: strings vs

end

instance : ToString Value := ⟨toM2String⟩

def elements? : Value → Option (List Value)
  | list xs | sequence xs => some xs
  | _ => none

end Value

namespace Error

def toM2String : Error → String
  | divByZero => "division by zero"
  | unboundVar x => s!"unbound variable '{x}'"
  | protectedSymbol x => s!"attempted to modify a protected symbol '{x}'"
  | noMethod op cs =>
    s!"no method for operator {op} applied to objects of class {", ".intercalate cs}"
  | conditionNotBoolean cls => s!"expected a Boolean condition, got {cls}"
  | indexOutOfBounds i n => s!"index {i} out of bounds for collection of length {n}"
  | immutableCollection cls => s!"cannot modify immutable {cls}"

instance : ToString Error := ⟨toM2String⟩
end Error

deriving instance DecidableEq for Except
end Macaulean.M2
