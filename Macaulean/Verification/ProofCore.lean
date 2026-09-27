import Macaulean.Verification.Frontend
import Macaulean.Verification.ProofData
import Macaulean.Verification.Evidence

/-!
# Fixed proof jobs and independent kernel acceptance

Intent is read, never granted, by this module. A worker may elaborate a candidate
in a disposable process. The acceptance path consumes only first-order proof data
and checks it synchronously in the unchanged environment, explicitly enabling the
kernel even when editor options request otherwise.
-/
namespace Macaulean.M2.Verification.ProofCore
open Lean Elab Command

structure Job where
  entry : Index.Entry
  proposal : Intent.Proposal
  target : Name
  payload : String

/-- Resolve the current source-attested target; never refresh approval tokens. -/
def approved (binding : String) (kind : Contracts.Kind) (digest : String) : CommandElabM Job := do
  let session ← DSL.getSession
  let index ← Index.get
  let some entry := index.find binding | throwError "binding is not in the semantic index"
  let theory ← Snapshot.theory
  let payload ← match Index.currentPayload entry kind session theory with
    | .ok p => pure p | .error e => throwError e
  let some p := index.ledger.find entry.id kind | throwError "no proposed contract for proof job"
  unless p.status (some payload) == .sourceAttested do
    throwError "proof jobs require current source-attested intent"
  unless p.digest == digest && Fingerprint.sha256 payload == digest do
    throwError "proof job fingerprint does not match the approved target"
  let some fn := session.lookup binding | throwError "proof binding is no longer visible"
  let target ← Targets.install kind fn ⟨session.env,session.heap⟩ digest
  return ⟨entry,p,target,payload⟩

def jobJson (job : Job) : Json := Json.mkObj [
  ("format",Json.str "macaulean.proof-job.v1"),
  ("bindingId",Json.str job.entry.id), ("binding",Json.str job.entry.name),
  ("schema",Json.str job.proposal.kind.name), ("digest",Json.str job.proposal.digest),
  ("target",Json.str job.target.toString),
  ("description",Json.str (Contracts.render job.proposal.kind)),
  ("source",Json.str job.entry.sourceText), ("resolvedCode",Json.str job.entry.declarationKey),
  ("proofStatus",Json.str "unattempted"), ("toolchain",Json.str Lean.versionString)]

def permittedAxioms : List String := ["propext","Classical.choice","Quot.sound"]

def audit (env : Environment) (target proof : Expr) : Except String Snapshot.Theory := do
  if proof.hasSorry || proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasLevelMVar then
    .error "proof has unresolved variables or sorry"
  let theory ← Snapshot.sealTheory env (Snapshot.exprNames target ++ Snapshot.exprNames proof)
  for ax in theory.axioms do
    unless ax ∈ permittedAxioms do .error s!"unapproved proof axiom: {ax}"
  for name in theory.declarations do
    let some c := env.find? name.toName | .error "missing proof dependency"
    if c.isUnsafe then .error s!"unsafe proof dependency: {name}"
  return theory

def packet (job : Job) (proof : Expr) : Except String Json := do
  return Json.mkObj [
    ("format",Json.str "macaulean.proof-packet.v1"),
    ("bindingId",Json.str job.entry.id), ("schema",Json.str job.proposal.kind.name),
    ("digest",Json.str job.proposal.digest), ("target",Json.str job.target.toString),
    ("term",← ProofData.encode proof)]

def decodePacket (job : Job) (data : Json) : Except String Expr := do
  for (key,value) in [("format","macaulean.proof-packet.v1"),
      ("bindingId",job.entry.id),("schema",job.proposal.kind.name),
      ("digest",job.proposal.digest),("target",job.target.toString)] do
    unless (← data.getObjValAs? String key) == value do
      .error s!"proof packet mismatch: {key}"
  ProofData.decode (← data.getObjVal? "term")

/-- Synchronous kernel checking. This deliberately bypasses asynchronous `addDecl`
reporting and never uses `debug.skipKernelTC` from the source file's options. -/
def check (job : Job) (proof : Expr) (source : String) : CommandElabM Evidence.Receipt := do
  let env ← getEnv
  let expected := mkConst job.target
  let theory ← match audit env expected proof with
    | .ok t => pure t | .error e => throwError e
  let proofDigest := Fingerprint.sha256 (Snapshot.exprKey proof)
  let name := `Macaulean.M2.CheckedProofs ++ Name.mkSimple ("p_" ++ job.proposal.digest ++ "_" ++ proofDigest)
  let declaration := Declaration.thmDecl {
    name, levelParams := [], type := expected, value := proof }
  if let some existing := env.find? name then
    match existing with
    | .thmInfo info =>
      unless info.type == expected && info.value == proof do throwError "proof name collision"
    | _ => throwError "proof name is not a theorem"
  else
    let next ← ofExceptKernelException (env.addDeclCore 50000000 65536 declaration none true)
    setEnv next
  let receipt : Evidence.Receipt := {
    bindingId := job.entry.id, schema := job.proposal.kind.name,
    targetDigest := job.proposal.digest, target := job.target.toString,
    theoremName := name.toString, proofDigest, dependencyDigest := theory.digest,
    axioms := theory.axioms, source }
  modifyEnv (Evidence.store · receipt)
  return receipt

/-- This function belongs only in the disposable elaboration process. No worker
source is executed by `check` or `decodePacket`. New helper declarations must be
reviewed imports, or expressed as local proof terms inside the candidate. -/
def elaborateCandidate (job : Job) (text : String) : CommandElabM Json := do
  let baseline ← getEnv
  try
    let parsed ← match Parser.runParserCategory baseline `term text with
      | .ok stx => pure stx | .error e => throwError "invalid proof term: {e}"
    let proof ← liftTermElabM do
      let e ← Term.elabTermEnsuringType parsed (some (mkConst job.target))
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
    let data ← match packet job proof with
      | .ok data => pure data | .error e => throwError e
    -- Audit against the ORIGINAL environment, not one modified by tactics.
    match audit baseline (mkConst job.target) proof with
    | .error e => throwError e
    | .ok _ => pure data
  finally
    setEnv baseline

end Macaulean.M2.Verification.ProofCore
