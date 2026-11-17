import MacauleanMathlib.GroebnerViews
import Macaulean.Verification.CertificateCommands

/-! Certify an actual worksheet candidate against the original exported ideal. -/
namespace Macaulean.M2.Verification.GroebnerCommands
open Lean Elab Command Meta
open Macaulean.Algebra MathematicalViews CertificateData GroebnerViews

private def checked (result : Except String α) : CommandElabM α :=
  match result with | .ok a => pure a | .error e => throwError e

private def lookup (binding : String) : CommandElabM Value := do
  let some value := (← DSL.getSession).lookup binding
    | throwError "unknown worksheet binding: {binding}"
  return value

private def define (name : Name) (value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    let type ← inferType value
    addAndCompile (.defnDecl {
      name, levelParams := [], type, value, hints := .regular 0, safety := .safe })

syntax (name := groebnerCommand) "#m2_groebner " str " for " str " as " ident : command

@[command_elab groebnerCommand]
def elabGroebner : CommandElab := fun stx => do
  let gBinding : TSyntax `str := ⟨stx[1]⟩
  let iBinding : TSyntax `str := ⟨stx[3]⟩
  let localName := stx[5].getId
  let root := (← getCurrNamespace) ++ localName
  for name in [root, root ++ `pairRows, root ++ `pairs_checked] do
    if (← getEnv).contains name then throwError "declaration already exists: {name}"
  let gv ← lookup gBinding.getString
  let iv ← lookup iBinding.getString
  let rv ← checked ((Polynomials.callPrimitive .ring iv).mapError toString)
  let r ← checked (readRing rv)
  let _ ← checked (readIdeal r iv)
  let G ← checked (readBasis r gv)
  let session ← DSL.getSession
  let fuel := m2.maxDepth.get (← getOptions)
  let values ← G.output.generators.mapM fun p =>
    G.output.generators.mapM fun q => do
      let s : RingPolynomial r := ⟨GroebnerCertificates.sPolynomial p.data q.data⟩
      checked (generateReductionRow fuel (polynomialValue s) (idealValue G.output)
        ⟨session.env,session.heap⟩)
  let rows ← checked (readPairRows r values)
  unless checkGroebner G rows do
    throwError "the candidate failed the monic S-pair and degree-bound checks"
  elabCommand (← `(#m2_ideal_equality $gBinding for $iBinding as $(mkIdent (localName ++ `idealEquality))))
  let eqRoot := root ++ `idealEquality
  let iExpr := mkConst (eqRoot ++ `ideal)
  let gExpr := mkConst (eqRoot ++ `basis)
  let ring ← liftTermElabM do return (← inferType iExpr).getAppArgs[0]!
  let rowExpr ← liftTermElabM <| mkAppM ``extract #[
    mkApp2 (mkConst ``readPairRows) ring (toExpr values)]
  define (root ++ `pairRows) rowExpr
  let rowsExpr := mkConst (root ++ `pairRows)
  liftTermElabM do
    let condition ← mkAppM ``checkGroebner #[gExpr, rowsExpr]
    let type ← mkEq condition (toExpr true)
    let proof ← Term.elabTerm (← `(by decide +kernel)) (some type)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    addDecl (.thmDecl { name := root ++ `pairs_checked, levelParams := [], type, value := proof })
    let result ← mkAppM ``checkGroebner_sound #[iExpr,gExpr,mkConst (eqRoot ++ `reverseRows),
      rowsExpr,mkConst (eqRoot ++ `checked),mkConst (root ++ `pairs_checked)]
    addDecl (.thmDecl { name := root, levelParams := [], type := ← inferType result, value := result })

end Macaulean.M2.Verification.GroebnerCommands
