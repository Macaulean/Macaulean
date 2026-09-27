# Stage 1: semantic indexing and intent approval

Stacked on PR #37 at `994f0cb978108f7177508218c60f5b3a3baae2e3`.
This is an opt-in verification frontend, not a new M2 execution engine.

## Start with ordinary M2

```lean
import Macaulean.Verification
open M2

keepPoly = p -> p;
```

Selecting the definition displays an M2 intent panel in Lean's normal InfoView.
Ordinary M2 outputs and errors remain unchanged. There is no agent connection,
model request, proof search, or network dependency in this implementation.

Choose a contract in the panel. The choice is initially empty: the system does
not infer intended behavior from a name or one observed call. The panel displays
the full deterministic description and inserts an explicit proposal command:

```lean
#m2_contract "keepPoly" polynomialIdentity
```

Review the input domain, successful-return guarantees, and exclusions. The
**Record approval in source** button remains disabled until the developer checks
that the displayed contract matches their intent. The button inserts
`#m2_approve` with the exact frozen fingerprint. It does not itself mutate the
ledger or show an optimistic success indicator. Lean re-elaboration recomputes
the target and validates the fingerprint before recording approval.

The command is inserted below the complete M2 input, not at a cursor that might
be inside a multiline function. A missing editor connection produces a copyable
command and an error notice. A changed revision clears consent synchronously;
there is no frame during which the prior revision's checkbox can approve it.

The following commands are also available:

```lean
#m2_status "keepPoly" polynomialIdentity
#m2_inspect "keepPoly"
#m2_revoke "keepPoly" polynomialIdentity
```

The panel exposes the exact named Lean proposition and can insert `#print` for
it. Target definitions use the namespace `Macaulean.M2.IntentTargets`. They are
**definitions of propositions**, not theorems or newly introduced axioms.
Existing target names must have exactly the expected body before they are reused.

To disable indexing for an input without changing its execution:

```lean
set_option m2.intent.enabled false in
x = 21;
```

Importing `Macaulean.Interpreter.DSL` instead of `Macaulean.Verification` retains
the original execution-only interface. Inside a namespace under `Macaulean.M2`,
write `open _root_.M2` to disambiguate the root syntax namespace.

## Intent and proof are different states

Intent can be proposed, source-attested, revoked, stale, or unavailable. Repeating
the identical proposal is idempotent and does not silently clear a revocation.
A changed proposal must be reviewed again. Missing bindings, broken dependency
references, unknown schemas, traversal exhaustion and mismatched tokens fail
closed.

The only proof status in stage 1 is **unattempted**. No command or RPC can change
that to verified. Approving a specification selects what should be proved; it
does not assume its truth. This branch does not approve any real project
contract. Approval tests use explicitly labelled synthetic fixtures.

A source attestation is also **not authentication of a human's identity**. Anyone
permitted to edit a Lean file can insert its text or run metaprogramming commands.
Repository review, or a later coordinator with separated permissions, must enforce
who may approve. The UI prevents accidental consent reuse; it is not a security
sandbox for adversarial Lean source.

## Initial mathematical vocabulary

All schemas have the formal shape

```text
for every admissible argument, evaluation depth, successful result and final state:
  Runtime.call depth function argument initialState = success(result, finalState)
  implies the schema's postcondition
```

They assert **partial correctness on successful returns**. A function that always
fails can satisfy such a proposition vacuously; error-freedom and termination
must be added as separate obligations before making a stronger claim. No schema
claims frame or effect preservation.

| Schema | Input domain | Successful-return guarantee |
| --- | --- | --- |
| `polynomialIdentity` | One polynomial in a specific runtime QQ polynomial ring | A polynomial in the same ring with identical coefficients. |
| `orderedRemainder` | `(f,G)` with same-ring polynomial generators in a list, sequence or generator row | `f-r` is in the generated ideal, and no nonzero term of `r` is divisible by a nonzero generator's leading monomial. |
| `linearCombination` | `(a,G)` with two same-ring polynomial rows of equal length | The returned polynomial is the sum of `a_i*G_i`, with no entries discarded. |

The remainder schema does **not** prescribe a particular reduction strategy,
unique representative or generator-order independence. The historical schema
identifier is `orderedRemainder`; its display title explicitly says
"Polynomial remainder (no canonical choice)". The fixed monomial order is the
polynomial layer's grevlex order. Scalar row entries require explicit promotion.

`Contracts.describe` and `Contracts.Post` are the reviewed presentation and formal
parts of this small vocabulary. Presentation is not generated by an LLM, but its
agreement with the mathematical definitions remains a review responsibility;
it is not established by printing an arbitrary natural-language description.
Both definitions are part of the semantic dependency seal.

## Checked views

`Views.Polynomial R` wraps the existing dimension-indexed polynomial representation
with a runtime ring index. `readPolynomial` validates exponent dimensions and the
full ring identity; separately created same-named rings are not conflated.

`Views.Row R n` contains exactly `n` polynomials in that ring. List, sequence and
generator-row decoders reject wrong dimensions or foreign entries. Scalars are
not silently specialized. These decoders have proved roundtrip, dimension and
foreign-ring laws.

Mathematical polynomial equality is coefficientwise: duplicate terms are summed,
and sparse-list order is not itself mathematical meaning. Product and row
combination coefficients use explicit finite convolution independent of the
production multiplication routine. These definitions do not, by themselves,
prove that every production arithmetic operation implements that meaning.

The views are a bridge to mathematical specifications, not yet a full Mathlib
commutative-ring instance, ideal library, verified lifting pass or VC generator.
Closures remain stateful lexical computations; no pure-function view is assumed.

## Source identity and snapshot policy

Every indexed binding has a module-qualified stable identifier, a generation,
original source text, resolved lexical code and nested UTF-8 syntax-node ranges.
Rebinding changes the generation. Formatting and source offsets are separate from
semantic identity. The underlying M2 input is evaluated exactly once; failed
inputs do not publish new bindings. Existing closure-cell changes are reflected
by current semantic snapshots even when the closure handle is unchanged.

Nested paths currently identify original syntax nodes, not independently proved
resolved-code program counters. Library entries expose the checked-in M2 library
text and resolved body but do not fabricate worksheet coordinates. Mapping
factory-produced closures back to their body origins is a later refinement.

Approval freezes the schema, exact formal target, resolved definition, reachable
bindings and the **entire initial runtime state**. The full state is conservative:
even an unrelated runtime write or fresh allocation invalidates the approval.
Until a frame/observational-irrelevance theorem exists, this is preferable to
silently asserting that omitted state cannot affect the target. Presentation
identifies snapshots at their source positions; a later input shows the current
status of watched contracts.

The semantic seal traverses Lean declaration types and bodies, universes,
constructors, inductives and recursor rules from the interpreter and contract
roots. Changing a named predicate's body therefore changes identity even when
the printed theorem name is unchanged. Missing declarations or exhausted
traversals do not yield a partial successful seal. The declaration/axiom inventory
is inspectable; listed axioms are existing dependencies, not approvals to trust
new assumptions.

The fingerprint is SHA-256 over length-framed constructor data, with known-vector
regressions including Unicode and multi-block input. It is not a signature. Live
records retain their exact payload; portable source attestations rely on the
usual collision-resistance assumption. The seal is deterministic metaprogramming
infrastructure, not a proved parser/translation soundness theorem.

Environment extensions are file-local and immutable. Importing another worksheet
does not import its M2 session, intent approvals, index or cached theory seal.
Ordinary named proposition definitions can be imported; that grants no approval
or proof. Reopening the source reconstructs the ledger by replaying its directives.

## Read-only tooling interface

`Macaulean.M2.Verification.Server.getSnapshot` is a Lean server RPC. Pass a
`{position, version}` query through the normal `$/lean/rpc/call` mechanism. A
mismatched document version is rejected. The response includes the URI, document
version, requested position, snapshot endpoint and semantic index. Clients must
discard a response if they have since observed another edit.

The index contains source ranges, resolved code, mathematical-view labels,
contract descriptions, exact target names, revision keys, intent statuses, event
counts and semantic dependency inventories. There is no approval or
proof-acceptance RPC. `Panel.inventory` is the deterministic environment-to-JSON
function; `Panel.getIndex` supplies its unwrapped position-relative form.

## Validation

The standard test driver retains all parent arithmetic, branching, collection,
closure, polynomial and Buchberger suites and adds:

- Decoder and coefficientwise-view tests, kernel examples and five independent
  SHA-256 vectors.
- Synthetic proposal/approval/revocation state-machine tests and negative controls
  for wrong bindings, schemas, tokens and stale payloads.
- Real interpreter fixtures for global changes, captured-cell aliases, recursion,
  comments, formatting and malformed handles.
- Immutable-environment forks that change a dependency body under the same name;
  target replacement with `True` or another schema must be rejected.
- An annotated M2 intent-review worksheet and separate import-isolation module.
- Eight interaction tests executing the exact JavaScript embedded in the InfoView
  widget: consent, revision changes, insertion anchors and failure handling.
- A real Lean language-server integration script for source attestations,
  versioned RPC, edits, comment-only replay, revocation and fresh-process replay.

The JavaScript component harness is not a browser-rendering test. Native LSP
integration does not claim a manually inspected VS Code screenshot. CI retains
exact logs, exit statuses, revisions and tool versions. The PR description records
completed validation at an exact head; uncompleted runs are not passing evidence.

## What is intentionally absent

No background agent loop, model/provider integration, contract inference,
proof-acceptance receipts, proof-success badges, universal algorithm theorem,
termination argument, frame theorem or trusted permission coordinator is added.
Those can now target explicit source-backed propositions and immutable snapshots,
without allowing a proof worker to redefine what counts as success.
