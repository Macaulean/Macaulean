import Macaulean.Verification
import Macaulean.Verification.ProofJobs.Checker
import Macaulean.Verification.ProofJobs.Identity

/-!
The editor creates jobs only from currently source-attested proposals. A proof
packet is replayed against the live binding and dependency seal; an old receipt
has no authority. The job path is tooling I/O, outside the pure M2 interpreter.
-/
namespace Macaulean.M2.Verification.ProofJobs
open Lean Elab Command

structure Evidence where
  bindingId : String
  kind : Contracts.Kind
  approvalDigest : String
  targetKey : String
  proofKey : String
  theoremName : Name
  deriving Inhabited

initialize evidenceExt : EnvExtension (List Evidence) ← registerEnvExtension (pure [])

/-- Recompute the seal instead of treating a cache as evidence of freshness. -/
def currentJob (bindingName : String) (kind : Contracts.Kind) : CommandElabM Job := do
  let session ← DSL.getSession
  let entry ← Index.ensure bindingName session
  let index ← Index.get
  let some proposal := index.ledger.find entry.id kind
    | throwError "propose and approve this contract before requesting proof work"
  let theory ← match Snapshot.sealTheory (← getEnv) Snapshot.roots with
    | .ok theory => pure theory | .error e => throwError e
  let payload ← match Index.currentPayload entry kind session theory with
    | .ok payload => pure payload | .error e => throwError e
  unless proposal.status (some payload) == .sourceAttested do
    throwError "proof work requires a current source-attested contract; no token is refreshed automatically"
  unless proposal.digest == Fingerprint.sha256 payload do throwError "corrupt approval digest"
  let some fn := session.lookup bindingName | throwError "approved binding is no longer visible"
  let target := Targets.statementExpr kind fn ⟨session.env,session.heap⟩
  let wire ← match Wire.encode target with
    | .ok wire => pure wire | .error e => throwError e
  return {
    jobId := proposal.digest, bindingId := entry.id, bindingName,
    schema := kind.name, approvalSource := proposal.approvalSource,
    approvalDigest := proposal.digest, theoryDigest := theory.digest,
    leanVersion := Lean.versionString, targetKey := Snapshot.exprKey target, target := wire }

private def kindArg (stx : Syntax) : CommandElabM Contracts.Kind := do
  let some kind := Contracts.Kind.parse stx.getId.toString
    | throwErrorAt stx "unknown contract schema"
  return kind

syntax (name := exportJobCommand) "#m2_export_proof_job " str ident str : command
syntax (name := replayJobCommand) "#m2_replay_proof " str ident str : command
syntax (name := proofStatusCommand) "#m2_proof_status " str ident : command

@[command_elab exportJobCommand]
def elabExportJob : CommandElab := fun stx => do
  let job ← currentJob (⟨stx[1]⟩ : TSyntax `str).getString (← kindArg stx[2])
  let path : System.FilePath := (⟨stx[3]⟩ : TSyntax `str).getString
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path ((toJson job).compress ++ "\n")
  logInfoAt stx s!"M2_PROOF_JOB_EXPORTED {job.jobId}; proof not yet checked"

@[command_elab replayJobCommand]
def elabReplayJob : CommandElab := fun stx => do
  let bindingName := (⟨stx[1]⟩ : TSyntax `str).getString
  let kind ← kindArg stx[2]
  let original ← getEnv
  try
    let job ← currentJob bindingName kind
    let path : System.FilePath := (⟨stx[3]⟩ : TSyntax `str).getString
    if (← path.metadata).byteSize.toNat > 16777216 then throwError "proof packet exceeds 16 MiB"
    let source ← IO.FS.readFile path
    if source.utf8ByteSize > 16777216 then throwError "proof packet exceeds 16 MiB"
    let packet : ProofPacket ← match Json.parse source >>= fromJson? with
      | .ok packet => pure packet | .error e => throwError e
    let receipt ← checkPacket job packet
    let theoremName ← match Wire.nameFromJson 32768 receipt.theoremRef with
      | .ok name => pure name | .error e => throwError e
    let record : Evidence := {
      bindingId := job.bindingId, kind, approvalDigest := job.approvalDigest,
      targetKey := job.targetKey, proofKey := receipt.proofKey, theoremName }
    modifyEnv fun env => evidenceExt.setState env
      (record :: (evidenceExt.getState env).filter fun old =>
        !(old.bindingId == record.bindingId && old.kind == record.kind))
    logInfoAt stx s!"{bindingName}: approved contract kernel-checked for revision {job.jobId}; termination and effect preservation are not claimed"
  catch error =>
    setEnv original
    throw error

@[command_elab proofStatusCommand]
def elabProofStatus : CommandElab := fun stx => do
  let bindingName := (⟨stx[1]⟩ : TSyntax `str).getString
  let kind ← kindArg stx[2]
  let job ← currentJob bindingName kind
  let records := evidenceExt.getState (← getEnv)
  match records.find? (fun r => r.bindingId == job.bindingId && r.kind == kind) with
  | none => logInfoAt stx s!"{bindingName}: no replayed proof"
  | some record =>
    if record.approvalDigest == job.approvalDigest && record.targetKey == job.targetKey then
      let some (.thmInfo info) := (← getEnv).find? record.theoremName
        | throwError "accepted theorem is no longer present in the current environment"
      unless Snapshot.exprKey info.type == job.targetKey &&
          Fingerprint.sha256 (Snapshot.exprKey info.value) == record.proofKey do
        throwError "accepted theorem no longer matches the recorded target and proof"
      logInfoAt stx s!"{bindingName}: kernel-checked partial correctness; theorem {record.theoremName}"
    else logInfoAt stx s!"{bindingName}: prior proof is stale"

end Macaulean.M2.Verification.ProofJobs
