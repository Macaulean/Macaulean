import Macaulean.Verification.Intent

/-!
# Exact, file-local proof evidence

Only the independent proof checker publishes receipts. A receipt neither grants
intent approval nor survives a changed target. It names an actual theorem, not a
worker verdict. Imported theorem declarations do not import this ledger.
-/
namespace Macaulean.M2.Verification.Evidence
open Lean

structure Receipt where
  bindingId : String
  schema : String
  targetDigest : String
  target : String
  theoremName : String
  proofDigest : String
  dependencyDigest : String
  axioms : List String
  source : String
  deriving Inhabited, Repr, ToJson, FromJson

initialize receiptsExt : EnvExtension (List Receipt) ← registerEnvExtension (pure [])

def find (env : Environment) (bindingId schema : String) : Option Receipt :=
  (receiptsExt.getState env).find? fun r => r.bindingId == bindingId && r.schema == schema

def store (env : Environment) (r : Receipt) : Environment :=
  receiptsExt.setState env (r :: (receiptsExt.getState env).filter fun old =>
    !(old.bindingId == r.bindingId && old.schema == r.schema))

/-- Presence of an attestation or a worker response is not evidence. The named
kernel theorem and its exact type must still be present in this environment. -/
def current (env : Environment) (p : Intent.Proposal) (payload : Option String) : Option Receipt := do
  let body ← payload
  if body != p.payload then none else do
    let r ← find env p.bindingId p.kind.name
    if r.targetDigest != p.digest then none else do
      let info ← env.find? r.theoremName.toName
      match info with
      | .thmInfo info =>
        if info.type == mkConst r.target.toName &&
            Fingerprint.sha256 (Snapshot.exprKey info.value) == r.proofDigest then some r
        else none
      | _ => none

end Macaulean.M2.Verification.Evidence
