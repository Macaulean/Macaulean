# Intent fingerprint representation

This supplements `m2-intent-stage1.md`. A fingerprint binds a review to a precise
formal target; it is not a proof and does not authenticate the reviewer.

## Exact expression structure without expansion

Lean expressions are directed acyclic graphs in memory. Generated declarations
can share large subexpressions. A naïve tree serialization duplicates those
subexpressions exponentially and can exhaust memory even for a small worksheet.

`ExpressionGraph` uses two caches:

1. A structural-expression map avoids revisiting shared input nodes.
2. An exact constructor-record map interns nodes after their children have been
   assigned indices. Equivalent allocation/sharing patterns yield the same table.

Map hashes accelerate lookup; hash collisions are resolved by equality, never
accepted as semantic identity. The serialized table records constructor tags,
child indices, constants, universe arguments, literals, binder modes, projections
and let flags. Bound indices replace binder names; metadata is deliberately
ignored. Names are serialized by their actual `Name` constructors, not by an
ambiguous pretty-printed dotted string.

The table and root indices are length-framed. The depth-30 shared-expression test
would have exponentially many tree occurrences but must use fewer than 100 table
nodes. Other controls distinguish binder modes, universes and different depths,
and preserve alpha-equivalence independently of allocation sharing.

## Complete declaration manifests

For each semantic declaration, the seal fingerprints its type, body (including
proof and opaque bodies when available), universe parameters, kind, safety flags,
and relevant inductive/constructor/recursor metadata. Recursor rule expressions
are encoded with the same structural graph machinery.

Every referenced declaration is scheduled once, including mutual-definition and
constructor edges. Missing declarations and exhausted traversal budgets fail
closed. This is not an optimization that discards proof dependencies.

The retained theory payload is a manifest of exact declaration names and their
SHA-256 digests, plus the Lean version and encoding version. Each leaf digest
covers that declaration's complete encoded data. The manifest itself has a root
SHA-256 digest. This avoids storing expanded declaration bodies in every proposal.
The declaration names and axiom inventory remain inspectable.

Consequently, integrity relies on SHA-256 collision resistance at both the leaf
and manifest levels. Live proposals retain the exact compact manifest and exact
runtime-expression encoding; they do not retain an unhashed duplicate of every
Lean declaration. Installing a named proposition additionally checks its actual
Lean type/body against the expected expression, not merely a name or digest.

## Runtime identity stays conservative

Reachable closures, globals, captured cells, library bodies and ring identities
are recorded, but no claim of observational irrelevance is assumed. The exact
formal target also freezes the complete runtime state. An unrelated write or
fresh allocation may therefore make approval stale. Relaxing that policy needs
a proved correspondence theorem, not a heuristic dependency filter.

Comment-only and formatting edits do not change resolved code identity. Real
function edits, captured-cell changes, callee changes, semantic predicate edits,
and different runtime rings must change the relevant target key. A new key cannot
inherit the prior card's consent checkbox or source attestation.

## Interactive execution

Lake precompiles the Macaulean library modules, including the opt-in verification
root, so metaprograms run as native compiled Lean code when imported. This is a
performance setting, not `native_decide`, a solver oracle, or a new axiom. Logical
definitions and the kernel's checks remain unchanged. The verification frontend
is still activated only by importing `Macaulean.Verification`; existing M2-only
worksheets keep the execution-only elaborator.

The SHA-256 implementation processes bytes without copying the message into
linked lists. Known vectors include empty, short, multi-block and UTF-8 inputs.
The complete CI suite also retains the parent kernel-execution tests. The real
Lean-server test checks approval replay in a new process, so process-local cache
or allocation identity cannot silently become the portable approval key.
