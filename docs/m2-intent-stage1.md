# Stage 1: semantic indexing and intent approval

This branch is stacked on PR #37 at `994f0cb978108f7177508218c60f5b3a3baae2e3`.

## Contract

Ordinary M2 execution remains unchanged. The opt-in verification frontend indexes
source definitions and their nested UTF-8 ranges, provides checked polynomial and
coefficient-row mathematical views, and presents a small versioned contract
vocabulary in Lean's InfoView. Intent approval is persisted as an explicit source
attestation tied to code, reachable bindings and semantic dependencies. It never
creates an axiom, proves an obligation, or starts an agent.

The first vocabulary covers polynomial identity, ordered polynomial remainder,
and a polynomial linear combination of a coefficient row and generator row.
Every contract is explicitly partial correctness on successful return. Safety,
termination and frame/effect properties are not silently claimed.

## Acceptance boundaries

- Specification proposal, approval, revocation and proof status are separate.
- A source attestation is not authentication of a human's identity. Repository
  review and later coordinator permissions must enforce who may approve.
- No real project contract is approved by the implementation agent. Tests use
  clearly labelled synthetic approvals only.
- Changed code, relevant global/captured values, formal predicates or semantic
  dependencies invalidate approval. Missing dependency information fails closed.
- The panel's mathematical descriptions come from the contract vocabulary, not
  an LLM paraphrase. Exact formal declarations remain inspectable.
- Source-backed approval commands replay on clean builds. File-local sessions and
  approvals are not silently imported from another worksheet's `.olean`.

Implementation, regressions and completed CI evidence will be documented here
as they land. This initial checkpoint is not a completion claim.
