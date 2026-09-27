# Reviewing intent from an M2 worksheet

This checklist is for Stage 1. It describes a working intent-review workflow, not
an agent service or an algorithm-verification result. Start with
[`Examples/IntentReview.lean`](../Examples/IntentReview.lean).

## Developer workflow

1. Import `Macaulean.Verification`, `open M2`, and write ordinary M2. Finish the
   runtime setup before approving a contract: this version deliberately freezes
   the complete initial runtime state.
2. Select a function's source position and choose a contract from its InfoView
   panel. There is no preselected contract and no inference from a function name
   or a successful example call. The proposal is an ordinary `#m2_contract`
   directive in the source file.
3. Review the complete input domain, return guarantee, and exclusions. Inspect
   the named Lean proposition when needed. In particular, the initial schemas
   claim only partial correctness on successful returns. An always-failing
   function is not ruled out, and termination/effect preservation are not claimed.
4. Check the explicit consent box, then use **Record approval in source**. The
   panel inserts an exact `#m2_approve` command. It does not grant approval through
   RPC or show success before that command has elaborated.
5. Keep the source directive in version control. A fresh Lean process reconstructs
   the approval by replay; importing the worksheet into another module does not
   transfer its approval ledger. `#m2_status` reports intent independently of
   proof status, which remains **unattempted** throughout Stage 1.

## Responding to an edit

A changed implementation, captured binding, initial state, schema, or semantic
dependency makes the old approval stale or unavailable. A comment-only edit need
not change the semantic fingerprint. A stale card describes the old reviewed
snapshot; it is not approval of the current one.

To review the new state, propose the contract again, inspect its current domain
and guarantee, and explicitly approve its new fingerprint. **Never auto-refresh
approval fingerprints as a build repair or proof-agent action.** Repeating an
identical proposal does not undo a revocation. Reapproval after revocation is a
new explicit consent event.

Approval identifies the target to prove; it does not establish that target.
A source attestation is not authenticated proof of a human identity. Repository
review or a later permissions-separated coordinator must enforce who may approve.
There are no source directives approving a real project contract in the shipped
example; automated approval fixtures are labelled as synthetic tests.

## Maintainer acceptance checks

| Surface | Required evidence |
| --- | --- |
| Runtime | The existing M2 input executes exactly once; failed inputs do not publish bindings. |
| Index | Module-qualified identity, binding generation, resolved code and nested original UTF-8 ranges. |
| Views | Polynomial ring identity and exponent dimensions are checked; coefficient rows cannot truncate. |
| Contracts | Deterministic description and actual `Prop` definition refer to the same reviewed schema. |
| Identity | Contract, exact runtime target, and declaration dependency bodies are sealed; missing data fails closed. |
| Approval | Wrong binding/schema/token is rejected; changed targets do not inherit consent; revocation survives identical reproposal. |
| UI | Consent resets on revision change; insertion is after the full input; failed edits cannot produce a success badge. |
| RPC | Requests identify the document version; stale requests are rejected; responses identify their source snapshot. |
| Replay | Approval is source-backed, reproducible after restart and isolated across imported worksheets. |
| Proof boundary | A target is a definition of `Prop`, not an axiom or theorem; intent approval cannot set proof status to verified. |

The row-view bridge additionally has general list/sequence roundtrip, wrong-length
rejection, and injectivity theorems in `Macaulean/Verification/ViewLaws.lean`.
These preserve the original polynomial data, not just printed forms. They are
representation theorems, not claims that any M2 algorithm has been verified.

## Reproducing validation

Run from the repository root under its pinned Lean toolchain:

```sh
lake build
lake build Macaulean.Verification MacauleanTest.VerificationViews \
  MacauleanTest.VerificationIntent MacauleanTest.VerificationDSL \
  MacauleanTest.VerificationImport MacauleanTest.VerificationWidget \
  MacauleanTest.VerificationGraph
lake env lean Examples/IntentReview.lean
python3 scripts/intent-lsp-test.py
lake test
```

The widget module test executes the actual embedded JavaScript using the checked-in
component harness. The language-server script exercises a real Lean server and
source re-elaboration. Neither test is a claim that a person inspected a running
VS Code window. CI stores separate logs and exit codes for focused tests, the user
example, LSP integration, and the complete retained suite.

See [Stage 1 architecture and boundaries](m2-intent-stage1.md) for the schema
semantics, conservative snapshot policy, dependency seal, and read-only RPC API.
