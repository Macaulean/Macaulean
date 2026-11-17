import Macaulean.Interpreter.DSL
import Macaulean.Verification.MathematicalViews

/-! Explicit mathematical exports of immutable worksheet snapshots, over both
QQ and checked prime fields. Each exported object has a kernel-checked equation
connecting it to the actual runtime value. -/
namespace Macaulean.M2.Verification.MathematicalExport
open Lean Elab Command Meta MathematicalViews

private def define (name : Name) (value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    if (← getEnv).contains name then throwError "declaration already exists: {name}"
    let type ← inferType value
    addAndCompile (.defnDecl {
      name, levelParams := [], type, value, hints := .regular 0, safety := .safe })

private def checkResult (result : Except String α) : CommandElabM Unit :=
  match result with | .ok _ => pure () | .error e => throwError e

private def ringDecoder (rv value : Value) (ideal : Bool) : CommandElabM Expr := do
  let r ← match readRing rv with | .ok r => pure r | .error e => throwError e
  if ideal then checkResult (readIdeal r value) else checkResult (readPolynomial r value)
  let ringExpr ← liftTermElabM <| mkAppM ``extract #[mkApp (mkConst ``readRing) (valueExpr rv)]
  return mkApp (mkConst (if ideal then ``readIdeal else ``readPolynomial)) ringExpr

syntax (name := exportCommand) "#m2_export " str " as " ident : command

/-- `.source` is the precise immutable runtime snapshot; `.source_eq` proves
that decoding that snapshot gives the exported mathematical presentation. -/
@[command_elab exportCommand]
def elabExport : CommandElab := fun stx => do
  let binding := (⟨stx[1]⟩ : TSyntax `str).getString
  let some source ← DefinitionExposure.latest binding
    | throwErrorAt stx "no worksheet binding exported for {binding}"
  let name := (← getCurrNamespace) ++ stx[3].getId
  for reserved in [name,name ++ `source,name ++ `source_eq] do
    if (← getEnv).contains reserved then throwErrorAt stx "declaration already exists: {reserved}"
  let sourceValue := mkConst (source ++ `value)
  let some value := (← DSL.getSession).lookup binding
    | throwErrorAt stx "worksheet binding is no longer available: {binding}"
  let decoder ← match value with
    | .algebra .rationals | .algebra (.finite (.field _)) =>
      checkResult (readField value)
      pure (mkConst ``readField)
    | .algebra (.ring _) | .algebra (.finite (.ring _)) =>
      checkResult (readRing value)
      pure (mkConst ``readRing)
    | .algebra (.poly r _) => ringDecoder (.algebra (.ring r)) value false
    | .algebra (.ideal r _) => ringDecoder (.algebra (.ring r)) value true
    | .algebra (.finite (.poly r _)) => ringDecoder (Finite.wrap (.ring r)) value false
    | .algebra (.finite (.ideal r _)) => ringDecoder (Finite.wrap (.ring r)) value true
    | _ => throwErrorAt stx "mathematical export expects a coefficient field, polynomial ring, polynomial, or ideal"
  let body ← liftTermElabM <| mkAppM ``extract #[mkApp decoder sourceValue]
  define name body
  define (name ++ `source) sourceValue
  liftTermElabM do
    let type ← inferType body
    let rhs := mkApp3 (mkConst ``Except.ok [0,0]) (mkConst ``String) type (mkConst name)
    let lhs := mkApp decoder (mkConst (name ++ `source))
    let eq ← mkEq lhs rhs
    let proof ← mkEqRefl rhs
    addDecl (.thmDecl { name := name ++ `source_eq, levelParams := [], type := eq, value := proof })

end Macaulean.M2.Verification.MathematicalExport
