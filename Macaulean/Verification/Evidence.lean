import Macaulean.Verification.Intent
import Macaulean.Verification.Targets

/-! Exact file-local evidence. A proof receipt neither grants intent approval
nor survives a changed target. Imported theorem declarations do not import receipts. -/
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
def current (env : Environment) (p : Intent.Proposal) (payload : Option String) : Option Receipt := do
  let body ← payload
  if body != p.payload then none else do
    let r ← find env p.bindingId p.kind.name
    if r.targetDigest != p.digest || r.target != (Targets.name p.digest).toString then none else do
      let info ← env.find? r.theoremName.toName
      match info with
      | .thmInfo info =>
        if info.type == mkConst (Targets.name p.digest) &&
            Fingerprint.sha256 (Snapshot.exprKey info.value) == r.proofDigest then some r
        else none
      | _ => none
end Macaulean.M2.Verification.Evidence
