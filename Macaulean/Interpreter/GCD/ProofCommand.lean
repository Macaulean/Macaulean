import Macaulean.Interpreter.GCD.Certificate
import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Check

/-! Named kernel-checked GCD certificates for existing worksheet values. -/
namespace Macaulean.M2.GCD
open Lean Elab Command

syntax (name := gcdProofCommand) "#m2_gcd_proof " ident str str str : command

@[command_elab gcdProofCommand]
def elabGCDProof : CommandElab := fun stx => do
  let session ← DSL.getSession
  let lookup (arg : Syntax) : CommandElabM Value := do
    let name := (⟨arg⟩ : TSyntax `str).getString
    let some value := session.lookup name | throwErrorAt arg "unknown worksheet binding {name}"
    return value
  let f ← lookup stx[2]
  let g ← lookup stx[3]
  let result ← lookup stx[4]
  match compute f g with
  | .error error => throwErrorAt stx "GCD validation/execution failed: {error.toM2String}"
  | .ok expected =>
    unless expected == result do
      throwErrorAt stx[4] "worksheet result does not equal the monic GCD"
  let name := (← getCurrNamespace) ++ stx[1].getId
  let fExpr := valueExpr f
  let gExpr := valueExpr g
  let resultExpr := valueExpr result
  let type := mkApp3 (mkConst ``ValueSpec) fExpr gExpr resultExpr
  let okResult := mkApp3 (mkConst ``Except.ok [0,0])
    (mkConst ``Error) (mkConst ``Value) resultExpr
  -- The kernel checks that `compute f g` reduces to the selected output.
  -- The preceding executable comparison only supplies an early diagnostic.
  liftTermElabM do
    let reflexivity ← Meta.mkEqRefl okResult
    let proof := mkApp4 (mkConst ``certify_result) fExpr gExpr resultExpr reflexivity
    addDecl (.thmDecl { name, levelParams := [], type, value := proof })
  logInfoAt stx m!"{name} : a kernel-checked monic GCD certificate for the selected worksheet values"

end Macaulean.M2.GCD
