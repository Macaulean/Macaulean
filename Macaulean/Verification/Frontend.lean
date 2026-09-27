import Macaulean.Verification.Panel

/-!
# Opt-in M2 verification frontend

Import `Macaulean.Verification`, then use ordinary `open M2` and ordinary M2.
The wrapper delegates execution to the existing elaborator exactly once. Intent
commands mutate only the verification index, never M2 bindings or Lean axioms.
-/
register_option m2.intent.enabled : Bool := {
  defValue := true
  descr := "Index M2 definitions and display intent panels (no proof search)." }

namespace Macaulean.M2.Verification.Frontend
open Lean Elab Command

@[command_elab M2.inputCommand]
def elabIndexedInput : CommandElab := fun stx => do
  if !(m2.intent.enabled.get (← getOptions)) then
    DSL.elabInput stx
  else
    let before ← DSL.getSession
    let (term,_) ← match DSL.lowerInput ⟨stx[0]⟩ with
      | .ok result => pure result | .error e => throwErrorAt stx e
    DSL.elabInput stx
    let after ← DSL.getSession
    let changed ← Index.record stx term before after
    for entry in changed do Panel.show entry stx

private def readKind (stx : Syntax) : CommandElabM Contracts.Kind := do
  let name := stx.getId.toString
  let some kind := Contracts.Kind.parse name
    | throwErrorAt stx "unknown M2 contract schema {name}"
  return kind

private def target (name : String) (kind : Contracts.Kind) : CommandElabM (Index.Entry × String) := do
  let session ← DSL.getSession
  let entry ← Index.ensure name session
  let theory ← Snapshot.theory
  let payload ← match Index.currentPayload entry kind session theory with
    | .ok payload => pure payload | .error e => throwError e
  return (entry,payload)

private def sourceLocation (stx : Syntax) : CommandElabM String := do
  let file ← getFileName
  let pos := (stx.getPos?.map (·.byteIdx)).getD 0
  return s!"{file}:byte:{pos}"

syntax (name := proposeCommand) "#m2_contract " str ident : command
syntax (name := approveCommand) "#m2_approve " str ident str : command
syntax (name := revokeCommand) "#m2_revoke " str ident : command
syntax (name := inspectCommand) "#m2_inspect " str : command
syntax (name := statusCommand) "#m2_status " str ident : command

@[command_elab proposeCommand]
def elabPropose : CommandElab := fun stx => do
  let name := stx[1].getString
  let kind ← readKind stx[2]
  let (entry,payload) ← target name kind
  let index ← Index.get
  Index.put { index with ledger := index.ledger.propose entry.id name kind payload }
  Panel.show entry stx

@[command_elab approveCommand]
def elabApprove : CommandElab := fun stx => do
  let name := stx[1].getString
  let kind ← readKind stx[2]
  let (entry,payload) ← target name kind
  let index ← Index.get
  let ledger ← match index.ledger.approve entry.id kind payload stx[3].getString (← sourceLocation stx) with
    | .ok ledger => pure ledger | .error e => throwErrorAt stx e
  Index.put { index with ledger }
  Panel.show entry stx
  logInfoAt stx s!"{name}: intent approved by source attestation; proof unattempted"

@[command_elab revokeCommand]
def elabRevoke : CommandElab := fun stx => do
  let name := stx[1].getString
  let kind ← readKind stx[2]
  let entry ← Index.ensure name (← DSL.getSession)
  let index ← Index.get
  let ledger ← match index.ledger.revoke entry.id kind (← sourceLocation stx) with
    | .ok ledger => pure ledger | .error e => throwErrorAt stx e
  Index.put { index with ledger }
  Panel.show entry stx
  logInfoAt stx s!"{name}: intent approval revoked; proof unattempted"

@[command_elab inspectCommand]
def elabInspect : CommandElab := fun stx => do
  let entry ← Index.ensure stx[1].getString (← DSL.getSession)
  Panel.show entry stx
  logInfoAt stx s!"{entry.name}: binding generation {entry.generation}; {entry.nodes.length} source nodes; proof unattempted"

@[command_elab statusCommand]
def elabStatus : CommandElab := fun stx => do
  let name := stx[1].getString
  let kind ← readKind stx[2]
  let (entry,payload) ← target name kind
  let index ← Index.get
  let some proposal := index.ledger.find entry.id kind
    | throwErrorAt stx "no contract proposed for {name}"
  logInfoAt stx s!"{name}: {(proposal.status (some payload)).label}; proof unattempted"

end Macaulean.M2.Verification.Frontend
