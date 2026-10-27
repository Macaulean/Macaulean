import Lean
import Macaulean.Interpreter.Value
import Macaulean.Interpreter.AlgebraExpr

/-! Literal quotation of runtime values, shared by worksheet exports and proof targets. -/
namespace Macaulean.M2
open Lean
mutual
def valueExpr : Value → Expr
  | .zz n => mkApp (mkConst ``Value.zz) (toExpr n)
  | .qq q => mkApp (mkConst ``Value.qq) (mkApp2 (mkConst ``mkRat) (toExpr q.num) (toExpr q.den))
  | .bool b => mkApp (mkConst ``Value.bool) (toExpr b)
  | .null => mkConst ``Value.null
  | .list xs => mkApp (mkConst ``Value.list) (valuesExpr xs)
  | .sequence xs => mkApp (mkConst ``Value.sequence) (valuesExpr xs)
  | .closure id => mkApp (mkConst ``Value.closure) (toExpr id)
  | .symbol name cell => mkApp2 (mkConst ``Value.symbol) (toExpr name) (toExpr cell)
  | .algebra a => mkApp (mkConst ``Value.algebra) (algebraObjectExpr a)
def valuesExpr : List Value → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Value)
  | v :: vs => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Value) (valueExpr v) (valuesExpr vs)
end
instance : ToExpr Value where
  toTypeExpr := mkConst ``Value
  toExpr := valueExpr
end Macaulean.M2
