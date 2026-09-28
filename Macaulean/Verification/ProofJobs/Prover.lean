import Macaulean.Verification.ProofJobs.Checker
import Macaulean.Verification.ProofJobs.Identity

/-!
Untrusted proof construction. This module may elaborate tactics and must run
inside the proof-worker sandbox. Its output is *not* acceptance evidence. The
separate Checker imports no candidate source and rechecks the serialized term.
-/
namespace Macaulean.M2.Verification.ProofJobs
open Lean Elab Command Term

syntax (name := synthesizeJobCommand) "#m2_synthesize_proof_job " str str str : command

@[command_elab synthesizeJobCommand]
def elabSynthesizeJob : CommandElab := fun stx => do
  let original ← getEnv
  let jobSource ← IO.FS.readFile (⟨stx[1]⟩ : TSyntax `str).getString
  let job : Job ← match Json.parse jobSource >>= fromJson? with
    | .ok job => pure job | .error e => throwError e
  let expected ← match checkedTarget job original with
    | .ok expected => pure expected | .error e => throwError e
  let candidate ← IO.FS.readFile (⟨stx[2]⟩ : TSyntax `str).getString
  if candidate.utf8ByteSize > 1048576 then throwError "proof candidate exceeds 1 MiB"
  let candidateStx ← match Parser.runParserCategory original `term candidate with
    | .ok parsedStx => pure parsedStx | .error e => throwError e
  let proof ← try
    let result ← liftTermElabM do
      let result ← elabTermEnsuringType candidateStx expected
      synthesizeSyntheticMVarsNoPostponing
      let result ← instantiateMVars result
      if result.hasMVar || result.hasFVar then throwError "unfinished proof candidate"
      return result
    pure result
  finally
    setEnv original
  match checkBaselineReferences original proof with
  | .error e => throwError e | .ok () => pure ()
  let encoded ← match Wire.encode proof with
    | .ok encoded => pure encoded | .error e => throwError e
  let packet : ProofPacket := { jobId := job.jobId, targetKey := job.targetKey, term := encoded }
  IO.FS.writeFile (⟨stx[3]⟩ : TSyntax `str).getString ((toJson packet).compress ++ "\n")
  logInfoAt stx "M2_PROOF_CANDIDATE_ONLY: independent kernel validation is still required"

end Macaulean.M2.Verification.ProofJobs
