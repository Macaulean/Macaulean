import Macaulean.Verification.ProofCore

/-! Source-backed replay accepts proof DATA only. `#m2_candidate` is a worker-side
command for disposable processes; it does not install proof evidence. -/
namespace Macaulean.M2.Verification.ProofCommands
open Lean Elab Command

private def text (stx : Syntax) : String := (⟨stx⟩ : TSyntax `str).getString
private def kind (stx : Syntax) : CommandElabM Contracts.Kind := do
  let some k := Contracts.Kind.parse stx.getId.toString | throwErrorAt stx "unknown contract schema"
  return k

def readLimited (path : String) (limit : Nat := 16777216) : IO String := do
  let metadata ← (System.FilePath.mk path).metadata
  if metadata.byteSize.toNat > limit then throw (IO.userError "proof input exceeds byte budget")
  IO.FS.readFile path

syntax (name := exportJob) "#m2_proof_job " str ident str : command
syntax (name := candidate) "#m2_candidate " str ident str " from " str " to " str : command
syntax (name := proofData) "#m2_proof " str ident str " := " str : command
syntax (name := proofFile) "#m2_proof " str ident str " from " str " sha256 " str : command

@[command_elab exportJob]
def elabJob : CommandElab := fun stx => do
  let job ← ProofCore.approved (text stx[1]) (← kind stx[2]) (text stx[3])
  logInfoAt stx ("M2_PROOF_JOB:" ++ (ProofCore.jobJson job).compress)

@[command_elab candidate]
def elabCandidate : CommandElab := fun stx => do
  let job ← ProofCore.approved (text stx[1]) (← kind stx[2]) (text stx[3])
  let candidateText ← readLimited (text stx[5])
  let data ← ProofCore.elaborateCandidate job candidateText
  IO.FS.writeFile (text stx[7]) data.compress
  logInfoAt stx "Proof candidate encoded; independent acceptance is still required."

def acceptData (stx : Syntax) (data source : String) : CommandElabM Unit := do
  let original ← getEnv
  try
    let job ← ProofCore.approved (text stx[1]) (← kind stx[2]) (text stx[3])
    unless data.utf8ByteSize ≤ 16777216 do throwError "proof packet exceeds byte budget"
    let parsed ← match Json.parse data with
      | .ok j => pure j | .error e => throwError "invalid proof packet JSON: {e}"
    let proof ← match ProofCore.decodePacket job parsed with
      | .ok e => pure e | .error e => throwError e
    let receipt ← ProofCore.check job proof source
    Panel.showPanel job.entry stx
    logInfoAt stx ("M2_PROOF_RECEIPT:" ++ (toJson receipt).compress)
  catch e =>
    setEnv original
    throw e

@[command_elab proofData]
def elabProofData : CommandElab := fun stx => do
  acceptData stx (text stx[5]) (← getFileName)

@[command_elab proofFile]
def elabProofFile : CommandElab := fun stx => do
  let file := text stx[5]
  let data ← readLimited file
  unless Fingerprint.sha256 data == text stx[7] do
    throwError "proof file digest changed; no evidence accepted"
  acceptData stx data file

end Macaulean.M2.Verification.ProofCommands
