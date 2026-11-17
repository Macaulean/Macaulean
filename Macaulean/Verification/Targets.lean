import Macaulean.Interpreter.RuntimeExpr
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

abbrev functionExpr := RuntimeExpr.functionExpr
abbrev functionsExpr := RuntimeExpr.functionsExpr
abbrev stateExpr := RuntimeExpr.stateExpr

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
