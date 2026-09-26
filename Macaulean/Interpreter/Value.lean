/-!
# Immutable runtime values

Lists and sequences remain distinct, including when nested or empty. The nested
inductive representation contains no references, identities, or mutable cells.
-/
namespace Macaulean.M2

inductive Value where
  | zz (n : Int)
  | qq (q : Rat)
  | bool (b : Bool)
  | null
  | list (elements : List Value)
  | sequence (elements : List Value)
  deriving DecidableEq, Repr, Inhabited

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
