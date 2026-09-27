import Macaulean.Verification.Snapshot

/-!
# Named formal targets, never assumed contracts

A proposal installs a definition of type Prop containing the exact function,
runtime state and schema. It installs no proof. The full first-order runtime state
is included in approval identity: until an observational-irrelevance theorem is
available, even an unrelated runtime write can conservatively stale an approval.
-/
namespace Macaulean.M2.Verification.Targets
open Lean Elab Command

deriving instance Lean.ToExpr for Contracts.Kind

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

def statementExpr (kind : Contracts.Kind) (fn : Value) (s : Runtime.State) : Expr :=
  mkApp3 (mkConst ``Contracts.Statement) (toExpr kind) (valueExpr fn) (stateExpr s)

def payload (theory : Snapshot.Theory) (id : String) (kind : Contracts.Kind)
    (fn : Value) (state : Runtime.State) : Except String String := do
  let reachable ← Snapshot.approvalPayload theory id kind fn state
  return Fingerprint.frame [reachable,theory.payload,Snapshot.exprKey (statementExpr kind fn state)]

def name (digest : String) : Name :=
  `Macaulean.M2.IntentTargets ++ Name.mkSimple ("t_" ++ digest)

/-- Existing declarations must have exactly the same body. Reusing a name is not
permission to replace or weaken its proposition. -/
def install (kind : Contracts.Kind) (fn : Value) (s : Runtime.State) (digest : String) : CommandElabM Name := do
  let n := name digest
  let type := mkSort .zero
  let value := statementExpr kind fn s
  if let some existing := (← getEnv).find? n then
    unless existing.type == type && existing.value? true == some value do
      throwError "intent target name is already bound to a different proposition"
  else
    liftTermElabM do
      addDecl (.defnDecl {
        name := n, levelParams := [], type, value,
        hints := .opaque, safety := .safe })
  return n

end Macaulean.M2.Verification.Targets
