/-!
# Runtime values of the Macaulay2 interpreter
-/

namespace Macaulean.M2

/-- Values of the supported fragment of Macaulay2.  `ZZ` and `QQ` are kept
distinct, as in Macaulay2: `7/7` is `1/1 : QQ`, not `1 : ZZ`. -/
inductive Value where
  /-- an element of `ZZ` -/
  | zz (n : Int)
  /-- an element of `QQ` -/
  | qq (q : Rat)
  /-- a `Boolean` -/
  | bool (b : Bool)
  /-- `null` -/
  | null
  deriving DecidableEq, Inhabited

/-- Runtime errors. -/
inductive Error where
  | divByZero
  | unboundVar (x : String)
  | protectedSymbol (x : String)
  /-- no method for an operator applied to values of these classes -/
  | noMethod (op : String) (classes : List String)
  deriving DecidableEq, Repr, Inhabited

namespace Value

/-- The name of the Macaulay2 class of a value. -/
def className : Value → String
  | zz _ => "ZZ" | qq _ => "QQ" | bool _ => "Boolean" | null => "Nothing"

/-- Imitates Macaulay2's `toExternalString`. -/
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

instance : ToString Error := ⟨toM2String⟩

end Error

deriving instance DecidableEq for Except

end Macaulean.M2
