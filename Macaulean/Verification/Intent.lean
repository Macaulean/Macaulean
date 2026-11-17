import Macaulean.Verification.Snapshot

/-!
# Intent is not evidence

The ledger contains specification targets and source attestations, not theorem
proofs. The source command is a deliberate approval action, but authenticating
its author requires repository review or a future authorized coordinator.
-/
namespace Macaulean.M2.Verification.Intent
open Contracts Fingerprint

inductive Review where
  | proposed | sourceAttested | revoked
  deriving Repr, DecidableEq, Inhabited
inductive Status where
  | proposed | sourceAttested | revoked | stale | unavailable
  deriving Repr, DecidableEq, Inhabited
/-- Stage 1 cannot create a checked-proof badge. -/
inductive ProofStatus where
  | unattempted
  deriving Repr, DecidableEq, Inhabited

structure Proposal where
  bindingId : String
  bindingName : String
  kind : Kind
  payload : String
  digest : String
  review : Review := .proposed
  approvalSource : String := ""
  deriving Repr, Inhabited

structure Event where
  bindingId : String
  kind : Kind
  action : Review
  digest : String
  source : String
  deriving Repr, Inhabited

structure Ledger where
  proposals : List Proposal := []
  events : List Event := []
  deriving Repr, Inhabited

def Ledger.find (l : Ledger) (id : String) (kind : Kind) : Option Proposal :=
  l.proposals.find? fun p => p.bindingId == id && p.kind == kind

def Ledger.store (l : Ledger) (p : Proposal) : Ledger :=
  { l with proposals := p :: l.proposals.filter (fun old =>
      !(old.bindingId == p.bindingId && old.kind == p.kind)) }

/-- Re-proposing the exact same payload is idempotent; a changed payload never
inherits an approval. Revocation remains explicit until a new approval action. -/
def Ledger.propose (l : Ledger) (id name : String) (kind : Kind) (payload : String) : Ledger :=
  match l.find id kind with
  | some p => if p.payload == payload then l else
      l.store ⟨id,name,kind,payload,sha256 payload,.proposed,""⟩
  | none => l.store ⟨id,name,kind,payload,sha256 payload,.proposed,""⟩

def Proposal.status (p : Proposal) (current : Option String) : Status :=
  match current with
  | none => .unavailable
  | some payload =>
    if payload != p.payload then .stale
    else match p.review with
      | .proposed => .proposed | .sourceAttested => .sourceAttested | .revoked => .revoked

def Proposal.proofStatus (_ : Proposal) : ProofStatus := .unattempted

/-- The client supplies a frozen token. The elaborator supplies the current
payload independently; the token cannot approve another code/specification pair. -/
def Ledger.approve (l : Ledger) (id : String) (kind : Kind)
    (current token source : String) : Except String Ledger := do
  let some p := l.find id kind | .error "propose a contract before approving it"
  unless p.payload == current do .error "stale contract proposal: code, bindings or semantics changed"
  unless token == p.digest && token == sha256 current do .error "approval fingerprint does not match the current target"
  let approved := { p with review := .sourceAttested, approvalSource := source }
  let next := l.store approved
  return { next with events := ⟨id,kind,.sourceAttested,token,source⟩ :: next.events }

def Ledger.revoke (l : Ledger) (id : String) (kind : Kind) (source : String) : Except String Ledger := do
  let some p := l.find id kind | .error "no contract to revoke"
  let next := l.store { p with review := .revoked, approvalSource := source }
  return { next with events := ⟨id,kind,.revoked,p.digest,source⟩ :: next.events }

def Status.label : Status → String
  | .proposed => "Proposed - intent not approved"
  | .sourceAttested => "Intent approved by source attestation"
  | .revoked => "Intent approval revoked"
  | .stale => "Stale - code, bindings or semantics changed"
  | .unavailable => "Unavailable - semantic snapshot could not be established"

theorem approval_is_not_a_proof (p : Proposal) : p.proofStatus = .unattempted := rfl

theorem unavailable_not_approved (p : Proposal) : p.status none = .unavailable := rfl

theorem changed_payload_is_stale (p : Proposal) (current : String) (h : current ≠ p.payload) :
    p.status (some current) = .stale := by
  simp [Proposal.status,h]

end Macaulean.M2.Verification.Intent
