import Macaulean.Verification.MathematicalExport
import Macaulean.Verification.CertificateData

/-! Worksheet certificate commands. Source execution proposes explicit rows;
closed kernel proofs check those rows before a theorem is published. -/
namespace Macaulean.M2.Verification.CertificateCommands
open Lean Elab Command Meta
open Macaulean.Algebra MathematicalViews CertificateData

private def checked (result : Except String α) : CommandElabM α :=
  match result with | .ok a => pure a | .error e => throwError e

private def lookup (binding : String) : CommandElabM Value := do
  let some value := (← DSL.getSession).lookup binding
    | throwError "unknown worksheet binding: {binding}"
  return value

private def define (name : Name) (value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    if (← getEnv).contains name then throwError "declaration already exists: {name}"
    let type ← inferType value
    addAndCompile (.defnDecl {
      name, levelParams := [], type, value, hints := .regular 0, safety := .safe })

private def theoremFrom (name : Name) (value : Expr) : CommandElabM Unit :=
  liftTermElabM do
    if (← getEnv).contains name then throwError "declaration already exists: {name}"
    addDecl (.thmDecl { name, levelParams := [], type := ← inferType value, value })

private def proveCheck (name : Name) (condition : Expr) : CommandElabM Expr :=
  liftTermElabM do
    let type ← mkEq condition (toExpr true)
    let proof ← Term.elabTerm (← `(by decide +kernel)) (some type)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    addDecl (.thmDecl { name, levelParams := [], type, value := proof })
    return mkConst name

private def exportBinding (binding : TSyntax `str) (name : Name) : CommandElabM Unit := do
  elabCommand (← `(#m2_export $binding as $(mkIdent name)))

private def exportedRing (polynomial : Name) : CommandElabM Expr :=
  liftTermElabM do
    let type ← inferType (mkConst polynomial)
    return type.getAppArgs[0]!

private def reserve (root : Name) (suffixes : List Name) : CommandElabM Unit := do
  for name in root :: suffixes.map (root ++ ·) do
    if (← getEnv).contains name then throwError "declaration already exists: {name}"

syntax (name := membershipCommand) "#m2_membership " str " in " str " as " ident : command

@[command_elab membershipCommand]
def elabMembership : CommandElab := fun stx => do
  let pBinding : TSyntax `str := ⟨stx[1]⟩
  let iBinding : TSyntax `str := ⟨stx[3]⟩
  let localName := stx[5].getId
  let root := (← getCurrNamespace) ++ localName
  reserve root [`polynomial,`polynomial.source,`polynomial.source_eq,
    `ideal,`ideal.source,`ideal.source_eq,`coefficients,`checked]
  let pv ← lookup pBinding.getString
  let iv ← lookup iBinding.getString
  let rv ← checked ((Polynomials.callPrimitive .ring iv).mapError toString)
  let r ← checked (readRing rv)
  let p ← checked (readPolynomial r pv)
  let I ← checked (readIdeal r iv)
  let session ← DSL.getSession
  let fuel := m2.maxDepth.get (← getOptions)
  let rowValues ← checked (generateRow fuel pv iv ⟨session.env,session.heap⟩)
  let row ← checked (readPolynomials r rowValues)
  unless checkMember p I row do
    throwError "the computed coefficient row does not prove ideal membership"
  exportBinding pBinding (localName ++ `polynomial)
  exportBinding iBinding (localName ++ `ideal)
  let ring ← exportedRing (root ++ `polynomial)
  let rowExpr ← liftTermElabM <| mkAppM ``extract #[
    mkApp2 (mkConst ``readPolynomials) ring (toExpr rowValues)]
  define (root ++ `coefficients) rowExpr
  let pExpr := mkConst (root ++ `polynomial)
  let iExpr := mkConst (root ++ `ideal)
  let rowExpr := mkConst (root ++ `coefficients)
  let condition ← liftTermElabM <| mkAppM ``checkMember #[pExpr,iExpr,rowExpr]
  let proof ← proveCheck (root ++ `checked) condition
  theoremFrom root (← liftTermElabM <| mkAppM ``checkMember_sound #[pExpr,iExpr,rowExpr,proof])

syntax (name := idealEqualityCommand) "#m2_ideal_equality " str " for " str " as " ident : command

@[command_elab idealEqualityCommand]
def elabIdealEquality : CommandElab := fun stx => do
  let gBinding : TSyntax `str := ⟨stx[1]⟩
  let iBinding : TSyntax `str := ⟨stx[3]⟩
  let localName := stx[5].getId
  let root := (← getCurrNamespace) ++ localName
  reserve root [`ideal,`ideal.source,`ideal.source_eq,`basis,`basisSource,
    `basis_source_eq,`reverseRows,`checked]
  let gv ← lookup gBinding.getString
  let iv ← lookup iBinding.getString
  let rv ← checked ((Polynomials.callPrimitive .ring iv).mapError toString)
  let r ← checked (readRing rv)
  let I ← checked (readIdeal r iv)
  let G ← checked (readBasis r gv)
  let session ← DSL.getSession
  let fuel := m2.maxDepth.get (← getOptions)
  let reverseValues ← I.generators.mapM fun p =>
    checked (generateRow fuel (polynomialValue p) (idealValue G.output) ⟨session.env,session.heap⟩)
  let reverseRows ← checked (readRows r reverseValues)
  unless checkIdealEquality I G reverseRows do
    throwError "the candidate rows do not prove equality of the two ideals"
  exportBinding iBinding (localName ++ `ideal)
  let ring ← liftTermElabM do return (← inferType (mkConst (root ++ `ideal))).getAppArgs[0]!
  let some source ← DefinitionExposure.latest gBinding.getString
    | throwError "no immutable worksheet snapshot for {gBinding.getString}"
  define (root ++ `basisSource) (mkConst (source ++ `value))
  let decoder := mkApp (mkConst ``readBasis) ring
  let decoded := mkApp decoder (mkConst (root ++ `basisSource))
  define (root ++ `basis) (← liftTermElabM <| mkAppM ``extract #[decoded])
  liftTermElabM do
    let basis := mkConst (root ++ `basis)
    let type ← inferType basis
    let rhs := mkApp3 (mkConst ``Except.ok [0,0]) (mkConst ``String) type basis
    let eqType ← mkEq decoded rhs
    let eqProof ← mkEqRefl rhs
    addDecl (.thmDecl { name := root ++ `basis_source_eq, levelParams := [], type := eqType, value := eqProof })
  define (root ++ `reverseRows) (← liftTermElabM <| mkAppM ``extract #[
    mkApp2 (mkConst ``readRows) ring (toExpr reverseValues)])
  let iExpr := mkConst (root ++ `ideal)
  let gExpr := mkConst (root ++ `basis)
  let rowsExpr := mkConst (root ++ `reverseRows)
  let condition ← liftTermElabM <| mkAppM ``checkIdealEquality #[iExpr,gExpr,rowsExpr]
  let proof ← proveCheck (root ++ `checked) condition
  theoremFrom root (← liftTermElabM <| mkAppM ``checkIdealEquality_sound #[iExpr,gExpr,rowsExpr,proof])

end Macaulean.M2.Verification.CertificateCommands
