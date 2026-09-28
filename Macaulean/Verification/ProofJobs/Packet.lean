import Macaulean.Verification.Targets
import Macaulean.Verification.ProofJobs.Wire

namespace Macaulean.M2.Verification.ProofJobs
open Lean

def protocol : String := "macaulean.proof-job.v1"

/-- Produced from a current source-attested proposal, not supplied by a worker.
The coordinator owns these bytes and mounts them read-only in both processes. -/
structure Job where
  format : String := protocol
  jobId : String
  bindingId : String
  bindingName : String
  schema : String
  approvalSource : String
  approvalDigest : String
  theoryDigest : String
  leanVersion : String
  targetKey : String
  target : Json
  deriving FromJson, ToJson

structure ProofPacket where
  format : String := "macaulean.proof-term.v1"
  jobId : String
  targetKey : String
  term : Json
  deriving FromJson, ToJson

/-- Diagnostic receipt, not a substitute for replaying the proof term. There is
no field by which a worker may select a different theorem or skip an obligation. -/
structure Receipt where
  format : String := "macaulean.proof-receipt.v1"
  jobId : String
  targetKey : String
  proofKey : String
  theoryDigest : String
  theoremName : String
  theoremRef : Json
  axioms : List String
  leanVersion : String
  status : String := "kernel-checked"
  deriving FromJson, ToJson

def acceptedAxioms : List String := ["propext", "Quot.sound", "Classical.choice"]

/-- Free term and universe metavariables are rejected before checking. The
kernel also rejects loose bound variables and undeclared universe parameters. -/
def closed (e : Expr) : Bool := !e.hasFVar && !e.hasMVar && !e.hasLevelMVar

def checkedTarget (job : Job) (env : Environment) : Except String Expr := do
  unless job.format == protocol do .error "unknown proof-job protocol"
  unless job.jobId == job.approvalDigest do .error "proof job is not its approved revision"
  unless job.leanVersion == Lean.versionString do .error "proof-job Lean version changed"
  let some kind := Contracts.Kind.parse job.schema | .error "unknown contract schema"
  unless !job.approvalSource.isEmpty do .error "proof job lacks source attestation"
  let theory ← Snapshot.sealTheory env Snapshot.roots
  unless theory.digest == job.theoryDigest do .error "proof-job semantic dependencies changed"
  let target ← Wire.decode 32768 job.target
  unless closed target do .error "proof target is not closed"
  unless Snapshot.exprKey target == job.targetKey do .error "proof target bytes changed"
  unless target.getAppFn == mkConst ``Contracts.Statement && target.getAppNumArgs == 3 do
    .error "proof job is not a complete approved contract"
  unless target.getAppArgs[0]! == toExpr kind do .error "contract schema and target disagree"
  return target

end Macaulean.M2.Verification.ProofJobs
