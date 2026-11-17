import Macaulean.Verification.ProofJobs.Packet
import Macaulean.Verification.ProofJobs.Identity
import Lean.AddDecl

/-!
The accepting command consumes kernel expressions, not tactic source. It is run
in a fresh process with the coordinator-owned baseline and target mounted
read-only. It forces synchronous kernel checking even when ambient Lean options
request otherwise. Failure restores the original environment, including after
Lean's declaration elaborator has installed an error-recovery axiom.
-/
namespace Macaulean.M2.Verification.ProofJobs
open Lean Elab Command

private def checkingOptions (o : Options) : Options :=
  (o.setBool `debug.skipKernelTC false).setBool `Elab.async false

/-- All constants must already exist in the accepting baseline. Worker-created
axioms, definitions and helper declarations cannot be smuggled in through a
compiled module. New reusable helper lemmas are reviewed/built separately. -/
def checkBaselineReferences (env : Environment) (proof : Expr) : Except String Unit := do
  unless closed proof do .error "proof packet contains an open expression"
  for name in Snapshot.exprNames proof do
    let some info := env.find? name | .error s!"proof requires an unreviewed declaration: {name}"
    if info.isUnsafe then .error s!"proof references an unsafe declaration: {name}"

/-- This function installs exactly one theorem with the coordinator's type.
No untrusted status field is interpreted as successful verification. -/
def checkPacket (job : Job) (packet : ProofPacket) : CommandElabM Receipt := do
  let original ← getEnv
  try
    unless packet.format == "macaulean.proof-term.v1" do throwError "unknown proof-term protocol"
    unless packet.jobId == job.jobId && packet.targetKey == job.targetKey do
      throwError "proof packet belongs to a different obligation or revision"
    let target ← match checkedTarget job original with
      | .ok target => pure target | .error e => throwError e
    let proof ← match Wire.decode 32768 packet.term with
      | .ok proof => pure proof | .error e => throwError e
    match checkBaselineReferences original proof with
    | .error e => throwError e | .ok () => pure ()
    let proofKey := Fingerprint.sha256 (Snapshot.exprKey proof)
    let theoremName ← liftTermElabM <| mkFreshUserName (`Macaulean.M2.CheckedProofs ++ Name.mkSimple ("p_" ++ job.jobId))
    liftTermElabM do
      withOptions checkingOptions do
        addDecl (.thmDecl {
          name := theoremName, levelParams := [], type := target, value := proof
        }) (forceExpose := true)
    let checked ← getEnv
    let some (.thmInfo info) := checked.find? theoremName
      | throwError "kernel checking did not produce the required theorem"
    unless info.type == target && info.value == proof do
      throwError "checked theorem does not have the required statement and proof"
    let dependencies ← match Snapshot.sealTheory checked [theoremName] with
      | .ok inventory => pure inventory | .error e => throwError e
    for axiomName in dependencies.axioms do
      unless axiomName ∈ acceptedAxioms do
        throwError "proof depends on an unapproved axiom: {axiomName}"
    return {
      jobId := job.jobId, targetKey := job.targetKey, proofKey,
      theoryDigest := job.theoryDigest, theoremName := theoremName.toString, theoremRef := Wire.nameToJson theoremName,
      axioms := dependencies.axioms, leanVersion := Lean.versionString }
  catch error =>
    setEnv original
    throw error

private def readJson (path : String) : CommandElabM Json := do
  let metadata ← (System.FilePath.mk path).metadata
  if metadata.byteSize.toNat > 16777216 then throwError "proof input exceeds 16 MiB"
  let source ← IO.FS.readFile path
  if source.utf8ByteSize > 16777216 then throwError "proof input exceeds 16 MiB"
  match Json.parse source with
  | .ok json => pure json | .error e => throwError e

private def readTyped [FromJson α] (path : String) : CommandElabM α := do
  match fromJson? (← readJson path) with
  | .ok result => pure result | .error e => throwError e

syntax (name := validateJobCommand) "#m2_validate_proof_job " str str str : command

@[command_elab validateJobCommand]
def elabValidateJob : CommandElab := fun stx => do
  let job : Job ← readTyped (⟨stx[1]⟩ : TSyntax `str).getString
  let packet : ProofPacket ← readTyped (⟨stx[2]⟩ : TSyntax `str).getString
  let receipt ← checkPacket job packet
  IO.FS.writeFile (⟨stx[3]⟩ : TSyntax `str).getString ((toJson receipt).compress ++ "\n")
  logInfoAt stx s!"M2_PROOF_KERNEL_CHECKED {receipt.jobId} {receipt.proofKey}"

end Macaulean.M2.Verification.ProofJobs
