import Macaulean.Verification.ProofJobs.Checker
import Macaulean.Verification.ProofJobs.Conservation
import Macaulean.Verification.ProofJobs.RuntimeReduction
import Macaulean.Interpreter.Functions

/-! All attestations in this module are synthetic test data. None approves a
project function. These tests require a real Lean kernel, not Python fixtures. -/
namespace Macaulean.M2.Verification.ProofJobs.Tests
open Lean Elab Command
set_option maxRecDepth 40000
set_option maxHeartbeats 40000000

private def fixture : Runtime.State := {
  heap := { functions := [.closure (.variadic "p") 1 (.read (.slot 0 0)) [[]]] } }

private def jobFor (s : Runtime.State) : CommandElabM Job := do
  let theory ← match Snapshot.sealTheory (← getEnv) Snapshot.roots with
    | .ok t => pure t | .error e => throwError e
  let target := Targets.statementExpr .polynomialIdentity (.closure 0) s
  let wire ← match Wire.encode target with
    | .ok j => pure j | .error e => throwError e
  return {
    jobId := Fingerprint.sha256 "SYNTHETIC KERNEL TEST ONLY",
    approvalDigest := Fingerprint.sha256 "SYNTHETIC KERNEL TEST ONLY",
    bindingId := Fingerprint.sha256 "synthetic-binding", bindingName := "toyIdentity",
    schema := "polynomialIdentity", approvalSource := "SYNTHETIC KERNEL TEST ONLY",
    theoryDigest := theory.digest, leanVersion := Lean.versionString,
    targetKey := Snapshot.exprKey target, target := wire }

private def packetFor (job : Job) (proof : Expr) : CommandElabM ProofPacket := do
  let term ← match Wire.encode proof with
    | .ok j => pure j | .error e => throwError e
  return { jobId := job.jobId, targetKey := job.targetKey, term }

private def mustReject (label : String) (action : CommandElabM α) : CommandElabM Unit := do
  let rejected ← try discard action; pure false catch _ => pure true
  unless rejected do throwError "negative control unexpectedly accepted: {label}"

run_cmd do
  let name := Name.num (Name.str .anonymous "literal.name") 17
  unless Wire.nameFromJson 100 (Wire.nameToJson name) == .ok name do
    throwError "name component identity was lost"
  let terms := [mkConst ``Nat, mkSort 0,
    Expr.lam `x (mkConst ``Nat) (.bvar 0) .default,
    Expr.forallE `x (mkConst ``Nat) (mkConst ``True) .implicit]
  for term in terms do
    let .ok encoded := Wire.encode term | throwError "cannot encode a closed expression"
    let .ok decoded := Wire.decode 100 encoded | throwError "cannot decode expression"
    unless term == decoded do throwError "expression constructor data changed"
  if (Wire.decode 100 (Wire.arr [toJson (999 : Nat)])).isOk then
    throwError "unknown wire tag accepted"
  if (Wire.decode 0 (Wire.arr [toJson (7 : Nat),toJson (0 : Nat)])).isOk then
    throwError "exhausted decoder accepted input"
  logInfo "STAGE2_WIRE_COMPLETE: names, universes, binders, closed terms and rejection"

run_cmd do
  let original ← getEnv
  let job ← jobFor fixture
  let target := Targets.statementExpr .polynomialIdentity (.closure 0) fixture
  let proof ← liftTermElabM do
    let candidateStx ← `(by
      apply Macaulean.M2.Verification.ProofJobs.Identity.contract
        (name := "p") (captured := [[]])
      rfl)
    let proof ← Term.elabTermEnsuringType candidateStx target
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars proof
  let packet ← packetFor job proof
  let receipt ← checkPacket job packet
  unless receipt.jobId == job.jobId && receipt.targetKey == job.targetKey do
    throwError "checker returned evidence for the wrong target"
  setEnv original
  logInfo "STAGE2_GENERIC_IDENTITY_COMPLETE: actual Runtime.call, all admissible arguments"

run_cmd do
  let original ← getEnv
  let job ← jobFor fixture
  let wrong ← packetFor job (mkConst ``True.intro)
  mustReject "wrong proposition" (checkPacket job wrong)
  withScope (fun s => { s with opts := s.opts.setBool `debug.skipKernelTC true }) do
    mustReject "skipKernelTC" (checkPacket job wrong)
  mustReject "wrong revision" (checkPacket job { wrong with jobId := "other" })
  mustReject "wrong target" (checkPacket job { wrong with targetKey := "other" })
  mustReject "schema replacement" (checkPacket { job with schema := "linearCombination" } wrong)
  let expected := Targets.statementExpr .polynomialIdentity (.closure 0) fixture
  let sorryProof := mkApp2 (mkConst ``sorryAx [0]) expected (toExpr false)
  mustReject "sorry" (checkPacket job (← packetFor job sorryProof))
  let missing ← packetFor job (mkConst `WorkerInventedProof)
  mustReject "worker declaration" (checkPacket job missing)
  let liar := `Macaulean.M2.Verification.ProofJobs.Tests.syntheticAxiom
  withScope (fun s => { s with opts := s.opts.setBool `Elab.async false }) do
    liftTermElabM do
      addDecl (.axiomDecl { name := liar, levelParams := [], type := expected, isUnsafe := false })
  mustReject "unapproved dependency" (checkPacket job (← packetFor job (mkConst liar)))
  setEnv original
  logInfo "STAGE2_KERNEL_NEGATIVE_CONTROLS_COMPLETE: wrong targets, options, holes and axioms"

example : Conservation.subtractRow (2 : Rat) [3,4] [5,6] = some [-7,-8] := by decide +kernel
example : Conservation.subtractRow (2 : Rat) [3] [] = none := by decide +kernel

end Macaulean.M2.Verification.ProofJobs.Tests
