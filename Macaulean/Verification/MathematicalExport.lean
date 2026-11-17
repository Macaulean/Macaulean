import Macaulean.Interpreter.DSL
import Macaulean.Verification.IdealView

/-! Explicit mathematical exports of immutable worksheet snapshots. -/
namespace Macaulean.M2.Verification.MathematicalExport
open Lean Elab Command Meta Views

private def define (name : Name) (value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    if (← getEnv).contains name then throwError "declaration already exists: {name}"
    let type ← inferType value
    addAndCompile (.defnDecl {
      name, levelParams := [], type, value, hints := .regular 0, safety := .safe })

private def polynomialExpr (r : Polynomials.RingInfo) (p : Views.Polynomial r) : Expr :=
  letI : ToExpr Rat := ⟨algebraRatExpr, mkConst ``Rat⟩
  mkApp2 (mkConst ``Views.Polynomial.mk) (algebraRingExpr r) (toExpr p.data)

private def idealExpr (r : Polynomials.RingInfo) (I : IdealPresentation r) : Expr :=
  let type := mkApp (mkConst ``Views.Polynomial) (algebraRingExpr r)
  let values := I.generators.foldr
    (fun p rest => mkApp3 (mkConst ``List.cons [0]) type (polynomialExpr r p) rest)
    (mkApp (mkConst ``List.nil [0]) type)
  mkApp2 (mkConst ``IdealPresentation.mk) (algebraRingExpr r) values

syntax (name := exportCommand) "#m2_export " str " as " ident : command

/-- `.source` is the precise immutable runtime snapshot; `.source_eq` proves
that decoding that snapshot gives the exported mathematical presentation. -/
@[command_elab exportCommand]
def elabExport : CommandElab := fun stx => do
  let binding := (⟨stx[1]⟩ : TSyntax `str).getString
  let some source ← DefinitionExposure.latest binding
    | throwErrorAt stx "no worksheet binding exported for {binding}"
  let name := (← getCurrNamespace) ++ stx[3].getId
  let sourceValue := mkConst (source ++ `value)
  let some value := (← DSL.getSession).lookup binding
    | throwErrorAt stx "worksheet binding is no longer available: {binding}"
  let (body, decoder) ← match value with
    | .algebra (.poly r _) =>
      match readPolynomial r value with
      | .error e => throwErrorAt stx e
      | .ok p => pure (polynomialExpr r p,
          mkApp (mkConst ``readPolynomial) (algebraRingExpr r))
    | .algebra (.ideal r _) =>
      match readIdeal r value with
      | .error e => throwErrorAt stx e
      | .ok I => pure (idealExpr r I, mkApp (mkConst ``readIdeal) (algebraRingExpr r))
    | _ => throwErrorAt stx "mathematical export currently expects a polynomial or ideal"
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
