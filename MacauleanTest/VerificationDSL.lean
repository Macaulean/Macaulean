import Macaulean.Verification

/-!
# An M2 developer's intent-review worksheet

No contract for production code is approved in this file. The fixture command
below synthesizes source attestations ONLY to exercise the exact production parser
and elaborator. Real users review the deterministic InfoView card and insert its
frozen `#m2_approve` command; no production autoapproval command exists.
-/
namespace Macaulean.M2.Verification.Worksheet
open Lean Elab Command
set_option maxRecDepth 40000
set_option maxHeartbeats 40000000

syntax (name := fixtureApproval) "#fixture_approve " str ident : command
@[command_elab fixtureApproval]
def elabFixtureApproval : CommandElab := fun stx => do
  let name := (⟨stx[1]⟩ : TSyntax `str).getString
  let some kind := Contracts.Kind.parse stx[2].getId.toString | throwError "invalid fixture schema"
  let index ← Index.get
  let some entry := index.find name | throwError "fixture binding was not indexed"
  let some p := index.ledger.find entry.id kind | throwError "fixture proposal missing"
  let source := s!"#m2_approve {repr name} {kind.name} {repr p.digest}"
  let parsed ← match Parser.runParserCategory (← getEnv) `command source with
    | .ok parsed => pure parsed | .error err => throwError "approval source did not parse: {err}"
  elabCommand parsed

open M2

-- The ordinary M2 command executes once; the opt-in index is a separate layer.
#guard_msgs in
keepPoly = p -> p;

#guard_msgs in
#m2_contract "keepPoly" polynomialIdentity

/-- info: keepPoly: Proposed - intent not approved; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

/-- error: approval fingerprint does not match the current target -/
#guard_msgs in
#m2_approve "keepPoly" polynomialIdentity "not-the-reviewed-revision"

-- A proposal creates a definition of a proposition, not a proof or an axiom.
run_cmd do
  let index ← Index.get
  let some entry := index.find "keepPoly" | throwError "missing semantic index entry"
  unless entry.generation == 1 && !entry.nodes.isEmpty do throwError "definition index incomplete"
  unless entry.sourceText.contains 'p' do throwError "original M2 source was not retained"
  let some p := index.ledger.find entry.id .polynomialIdentity | throwError "missing proposal"
  let some declaration := (← getEnv).find? (Targets.name p.digest) | throwError "formal target missing"
  unless declaration.isDefinition && !declaration.isAxiom && declaration.type == mkSort .zero do
    throwError "proposal is not an unproved proposition definition"
  let session ← DSL.getSession
  let some fn := session.lookup "keepPoly" | throwError "function missing"
  unless declaration.value? true == some (Targets.statementExpr .polynomialIdentity fn ⟨session.env,session.heap⟩) do
    throwError "named proposition differs from the reviewed snapshot"
  unless p.proofStatus == .unattempted do throwError "approval fabricated proof evidence"

/-- info: keepPoly: intent approved by source attestation; proof unattempted -/
#guard_msgs in
#fixture_approve "keepPoly" polynomialIdentity

/-- info: keepPoly: Intent approved by source attestation; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

-- No M2 execution occurs in the approval commands, so input numbering is unchanged.
run_cmd do
  unless (← DSL.getSession).nextInput == 2 do throwError "approval executed an M2 input"

-- Until a frame/irrelevance theorem is proved, all runtime changes conservatively
-- invalidate the exact frozen-state target, including this unrelated write.
#guard_msgs in
unrelated = 17;

/-- info: keepPoly: Stale - code, bindings or semantics changed; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

/-- error: stale contract proposal: code, bindings or semantics changed -/
#guard_msgs in
#fixture_approve "keepPoly" polynomialIdentity

#guard_msgs in
#m2_contract "keepPoly" polynomialIdentity

/-- info: keepPoly: Proposed - intent not approved; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

/-- info: keepPoly: intent approved by source attestation; proof unattempted -/
#guard_msgs in
#fixture_approve "keepPoly" polynomialIdentity

/-- info: keepPoly: intent approval revoked; proof unattempted -/
#guard_msgs in
#m2_revoke "keepPoly" polynomialIdentity

/-- info: keepPoly: Intent approval revoked; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

-- Re-proposing exactly the same target cannot silently clear a revocation.
#guard_msgs in
#m2_contract "keepPoly" polynomialIdentity

/-- info: keepPoly: Intent approval revoked; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

-- Rebinding produces a distinct generation while retaining the binding's identity.
#guard_msgs in
keepPoly = p -> p + 1;

/-- info: keepPoly: Stale - code, bindings or semantics changed; proof unattempted -/
#guard_msgs in
#m2_status "keepPoly" polynomialIdentity

run_cmd do
  let index ← Index.get
  let some entry := index.find "keepPoly" | throwError "rebinding lost index entry"
  unless entry.generation == 2 do throwError "rebinding did not change generation"
  unless entry.id == Snapshot.bindingId (← getEnv).mainModule "keepPoly" do
    throwError "source offset or rebinding changed stable identity"

-- Nested UTF-8 syntax is preserved for future source-linked proof obligations.
#guard_msgs in
choosePoly = (p,q) -> (
  -- λ, 中文: original bytes rather than character offsets
  if p == 0 then q else (copy := p; copy));

run_cmd do
  let index ← Index.get
  let some entry := index.find "choosePoly" | throwError "nested definition missing"
  unless entry.nodes.any (fun n => n.kind == "Macaulean.M2.DSL.ifElse") do
    throwError "nested conditional range missing"
  unless entry.nodes.any (fun n => n.kind == "Macaulean.M2.DSL.localAssign") do
    throwError "nested lexical binding range missing"
  let text := (← getFileMap).source
  for node in entry.nodes do
    unless node.startByte ≤ node.stopByte && node.stopByte ≤ text.utf8ByteSize do
      throwError "invalid source byte range"
  unless (Index.sourceNodes 0 Syntax.missing).isError do throwError "partial source map accepted"

-- Checked polynomial/row views are available for actual M2 values.
#guard_msgs in
R = QQ[x,y];
#guard_msgs in
p = x^2 + y;
#guard_msgs in
row = gens ideal(p,y);
run_cmd do
  let s ← DSL.getSession
  let some p := s.lookup "p" | throwError "polynomial binding missing"
  let some row := s.lookup "row" | throwError "row binding missing"
  unless (Index.viewLabels p).head? == some "Checked ring-indexed polynomial view" do
    throwError "polynomial view not displayed"
  unless (Index.viewLabels row).head? == some "Checked dimension-indexed coefficient/generator row" do
    throwError "row view not displayed"

-- Indexing can be disabled without changing execution or introducing a second run.
set_option m2.intent.enabled false in
#guard_msgs in
disabled = 21;
run_cmd do
  unless (← DSL.getSession).lookup "disabled" == some (.zz 21) do throwError "disabled frontend changed execution"
  unless ((← Index.get).find "disabled").isNone do throwError "disabled input was indexed"

-- Lean remains Lean, and no user theorem is needed for normal M2 evaluation.
example : 2 + 2 = 4 := rfl

run_cmd do
  logInfo "INTENT_WORKSHEET_COMPLETE: source approval, stale edits, revocation, rebinding, views and UTF-8 indexing"

end Macaulean.M2.Verification.Worksheet
