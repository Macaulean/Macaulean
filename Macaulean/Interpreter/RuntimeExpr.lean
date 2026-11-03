import Macaulean.Interpreter.ValueExpr
import Macaulean.Interpreter.LibraryCompiler
import Macaulean.Interpreter.Runtime

/-! Closed, kernel-checkable snapshots; handles retain their original heap. -/
namespace Macaulean.M2.RuntimeExpr
open Lean
mutual
def functionExpr : Runtime.Function → Expr
  | .closure params slots body captured =>
    mkApp4 (mkConst ``Runtime.Function.closure) (toExpr params) (toExpr slots)
      (LibraryCompiler.codeExpr body) (toExpr captured)
  | .composition a b => mkApp2 (mkConst ``Runtime.Function.composition) (valueExpr a) (valueExpr b)
  | .predicate op a b => mkApp3 (mkConst ``Runtime.Function.predicate) (toExpr op) (valueExpr a) (valueExpr b)
  | .negated f => mkApp (mkConst ``Runtime.Function.negated) (valueExpr f)
def functionsExpr : List Runtime.Function → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Runtime.Function)
  | f::fs => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Runtime.Function)
      (functionExpr f) (functionsExpr fs)
end

def stateExpr (s : Runtime.State) : Expr :=
  let heap := mkApp3 (mkConst ``Runtime.Heap.mk) (toExpr s.heap.cells)
    (functionsExpr s.heap.functions) (toExpr s.heap.nextRing)
  mkApp2 (mkConst ``Runtime.State.mk) (toExpr s.env) heap

end Macaulean.M2.RuntimeExpr
