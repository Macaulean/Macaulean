/-!
# Runtime values of the Macaulay2 interpreter
-/

namespace Macaulean.M2

/-- `ZZ` and `QQ` remain distinct even for integral-valued rationals. -/
inductive Value where
  | zz (n : Int)
  | qq (q : Rat)
  | bool (b : Bool)
  | null
  deriving DecidableEq, Inhabited

inductive Error where
  | divByZero
  | unboundVar (x : String)
  | protectedSymbol (x : String)
  | noMethod (op : String) (classes : List String)
  | conditionNotBoolean (actualClass : String)
  deriving DecidableEq, Repr, Inhabited

namespace Value

def className : Value → String
  | zz _ => "ZZ" | qq _ => "QQ" | bool _ => "Boolean" | null => "Nothing"

def toM2String : Value → String
  | zz n => toString n
  | qq q => s!"{q.num}/{q.den}"
  | bool b => toString b
  | null => "null"

instance : ToString Value := ⟨toM2String⟩

instance : Repr Value where
  reprPrec
    | zz n, p => Repr.addAppParen ("Value.zz " ++ reprArg n) p
    | qq q, p => Repr.addAppParen ("Value.qq " ++ reprArg q) p
    | bool b, p => Repr.addAppParen ("Value.bool " ++ reprArg b) p
    | null, _ => "Value.null"

end Value

namespace Error

def toM2String : Error → String
  | divByZero => "division by zero"
  | unboundVar x => s!"unbound variable '{x}'"
  | protectedSymbol x => s!"attempted to modify a protected symbol '{x}'"
  | noMethod op cs =>
    s!"no method for operator {op} applied to objects of class {", ".intercalate cs}"
  | conditionNotBoolean cls => s!"expected a Boolean condition, got {cls}"

instance : ToString Error := ⟨toM2String⟩

end Error

deriving instance DecidableEq for Except

end Macaulean.M2
