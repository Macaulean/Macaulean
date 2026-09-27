import Macaulean.Verification

/-!
# Synthetic intent-approval regression tests

No real project contract is approved here. Every attestation below is a synthetic
fixture exercising the independent intent state machine and semantic identities.
-/
namespace Macaulean.M2.Verification.IntentTests
open Lean Elab Command Intent
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

run_cmd do
  let id := "synthetic-binding"
  let payload := "synthetic exact target"
  let kind := Contracts.Kind.polynomialIdentity
  let token := Fingerprint.sha256 payload
  let initial : Ledger := {}
  unless (initial.approve id kind payload token "TEST ONLY").isError do
    throwError "approval without a proposal succeeded"
  let proposed := initial.propose id "synthetic" kind payload
  let some p := proposed.find id kind | throwError "proposal missing"
  unless p.status (some payload) == .proposed && p.proofStatus == .unattempted do
    throwError "a proposal acquired approval or evidence"
  for (key,body,digest) in [(id,payload,"wrong"),(id,"changed",token),("other",payload,token)] do
    unless (proposed.approve key kind body digest "TEST ONLY").isError do
      throwError "mismatched approval accepted"
  unless (proposed.approve id .orderedRemainder payload token "TEST ONLY").isError do
    throwError "approval changed the schema"
  let .ok approved := proposed.approve id kind payload token "TEST ONLY"
    | throwError "exact synthetic approval failed"
  let some p := approved.find id kind | throwError "approved record missing"
  unless p.status (some payload) == .sourceAttested && p.proofStatus == .unattempted do
    throwError "intent and evidence conflated"
  unless p.status (some "changed") == .stale && p.status none == .unavailable do
    throwError "stale or unavailable target remained approved"
  let same := approved.propose id "synthetic" kind payload
  unless (same.find id kind).map (·.review) == some .sourceAttested do
    throwError "identical reproposal is not idempotent"
  let changed := approved.propose id "synthetic" kind "changed"
  unless (changed.find id kind).map (·.review) == some .proposed do
    throwError "a changed proposal inherited approval"
  let .ok revoked := approved.revoke id kind "TEST REVOKE" | throwError "revocation failed"
  unless (revoked.find id kind).map (fun p => p.status (some payload)) == some .revoked do
    throwError "revocation not reflected"
  unless (revoked.propose id "synthetic" kind payload).find id kind |>.map (·.review) == some .revoked do
    throwError "reproposal silently undid revocation"
  unless approved.events.length == 1 && revoked.events.length == 2 do
    throwError "approval audit events missing"
  logInfo "INTENT_LEDGER_COMPLETE: proposal, exact approval, revocation, replay and failure controls"

private def execute (s : Session) (source : String) : Except String Session := do
  let term ← parse source
  let result := s.step term true
  match result.outcome with
  | .ok _ => return result.session
  | .error e => .error e.toM2String

private def key (s : Session) (name : String) : Except String String := do
  let some v := s.lookup name | .error "missing synthetic function"
  Snapshot.reachable v ⟨s.env,s.heap⟩

run_cmd do
  let .ok original := execute {} "offset=3;f=x->x+offset" | throwError "fixture failed"
  let .ok before := key original "f" | throwError "missing dependency key"
  let .ok updated := execute original "offset=4" | throwError "fixture update failed"
  let .ok after := key updated "f" | throwError "updated dependency key failed"
  unless before != after do throwError "global dependency change was lost"
  let .ok unrelated := execute original "unrelated=123" | throwError "unrelated fixture failed"
  let .ok same := key unrelated "f" | throwError "unrelated key failed"
  unless before == same do throwError "reachable graph includes an unreachable global"
  unless Snapshot.exprKey (Targets.stateExpr ⟨original.env,original.heap⟩) !=
      Snapshot.exprKey (Targets.stateExpr ⟨unrelated.env,unrelated.heap⟩) do
    throwError "exact snapshot discarded an unrelated state change without a proof"
  let .ok counters := execute {} "make=start->(n:=start;()->(n=n+1));c=make 0;alias=c"
    | throwError "captured cell fixture failed"
  let .ok first := key counters "c" | throwError "captured key failed"
  let .ok incremented := execute counters "alias()" | throwError "alias call failed"
  let .ok second := key incremented "c" | throwError "updated captured key failed"
  unless first != second do throwError "captured-cell alias mutation was lost"
  let .ok recursive := execute {} "rec=n->if n==0 then 0 else rec(n-1)"
    | throwError "recursion fixture failed"
  unless (key recursive "rec").isOk do throwError "recursive dependency graph did not terminate"
  unless (Snapshot.reachable (.closure 999) {}).isError do throwError "invalid handle accepted"
  unless (Snapshot.reachable (.symbol "bad" 999) {}).isError do throwError "invalid captured cell accepted"
  unless Snapshot.bindingId `ModuleA "f" != Snapshot.bindingId `ModuleB "f" do
    throwError "module-qualified binding collision"
  let .ok a := parse "f=x->x+1" | throwError "parser fixture failed"
  let .ok b := parse "f = x -> (x + 1) -- a comment" | throwError "format fixture failed"
  unless Snapshot.exprKey (LibraryCompiler.codeExpr (Lexical.prepare a).1) ==
      Snapshot.exprKey (LibraryCompiler.codeExpr (Lexical.prepare b).1) do
    throwError "comments or formatting changed resolved-code identity"
  logInfo "INTENT_DEPENDENCIES_COMPLETE: globals, captured aliases, recursion, invalid handles and exact state"

-- Fork immutable Lean environments to change a dependency's body under the same
-- name. A name-only or theorem-text-only fingerprint would fail this test.
run_cmd do
  let original ← getEnv
  let name := `Macaulean.M2.Verification.IntentTests.syntheticDefinition
  let add (n : Nat) : CommandElabM Unit := liftTermElabM do
    addDecl (.defnDecl { name, levelParams := [], type := mkConst ``Nat,
      value := toExpr n, hints := .opaque, safety := .safe })
  add 1
  let .ok first := Snapshot.seal (← getEnv) [name] | throwError "first theory seal failed"
  setEnv original
  add 2
  let .ok second := Snapshot.seal (← getEnv) [name] | throwError "second theory seal failed"
  unless first.digest != second.digest && first.payload != second.payload do
    throwError "changed declaration body retained approval identity"
  unless (Snapshot.seal (← getEnv) [`MissingSemanticDefinition]).isError do
    throwError "missing semantic dependency silently ignored"
  setEnv original
  logInfo "INTENT_THEORY_SEALS_COMPLETE: changed definition bodies and missing dependencies"

end Macaulean.M2.Verification.IntentTests
