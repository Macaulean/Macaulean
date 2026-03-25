# CAS Architecture

This document describes the CAS backend architecture being implemented on the `cas-architecture` branch.

It has two purposes:

- define the design we want for Lean-to-CAS integration in this repo
- record what is actually implemented today

## Goals

The architecture is meant to support multiple computer algebra backends, not just Macaulay2.

The core requirements are:

- Lean remains the trust boundary.
- CAS backends compute artifacts and certificates, but do not directly produce trusted theorems.
- Mathematical data is transported in a backend-neutral format based on MRDI.
- Backends advertise semantic capabilities such as factorization or quotient-remainder, not ad hoc RPC names.
- Results can be chained: one checked artifact or judgment can feed later steps.
- Discharge is explicit: certificate checking and theorem closing are separate layers.

## Trust Model

The intended trust model is:

1. Lean reifies the relevant mathematical objects.
2. A backend computes a result and returns artifacts plus an explicit certificate.
3. Lean checks the certificate against the transported artifacts.
4. Lean derives user-facing judgments from the checked certificate.
5. Tactics close goals only from checked or derived judgments.

The kernel trusts only Lean definitions, proof terms, and the certificate checkers/dischargers implemented in Lean.

## Architectural Layers

The current design is split into four layers.

### 1. Data Plane: MRDI

MRDI is the canonical interchange format for mathematical objects.

The repo currently uses MRDI for:

- scalar payloads
- sparse commutative polynomial payloads
- ideals by generators
- semantic CAS artifacts and certificates

The branch also moves the local Lean implementation closer to the published MRDI container spec:

- `_ns` is optional
- `"_refs"` is read and written
- parameterized `_type` descriptors can carry general JSON parameters
- reference resolution is implemented

### 2. Semantic CAS Layer

This layer defines backend-neutral concepts:

- artifacts
- judgments
- certificates
- provenance
- tasks and capabilities

It is deliberately phrased in semantic terms such as `factor` or `quotientRemainder`, not backend method names.

### 3. Execution and Chaining

This layer executes typed chain steps:

- resolve artifact references
- call a backend
- record returned artifacts, judgments, and certificates
- check certificates
- optionally derive new judgments using dischargers

This turns backend interaction into a replayable proof/dataflow graph instead of a monolithic tactic.

### 4. Tactic / Theorem Layer

User-facing tactics and helper APIs sit on top of checked and derived judgments.

They are intentionally thin:

- gather or reify Lean terms
- call a semantic backend task
- consume checked/derived outputs
- finish with a small Lean proof script

## MRDI Profile in This Repo

The current branch does not try to redefine MRDI itself. Instead it defines a repo-specific profile on top of MRDI.

That profile currently includes:

- exact scalar objects such as `Nat`, `Int`, `String`, `Bool`
- exact sparse commutative polynomials
- ideals by generator lists
- semantic CAS artifacts
- judgments such as factorization, quotient-remainder, ideal membership, and nonnegativity
- certificates such as factorization and quotient-remainder witnesses

The most important missing long-term piece is richer ambient context objects. At the moment, polynomial payloads still carry less ambient structure than the final design wants.

## Backend Interface

The backend-facing API is semantic and capability-driven.

Backends advertise `Capability` objects that describe:

- task kind
- exact vs unsupported
- certificate-bearing vs oracle-style
- deterministic vs heuristic
- supported input and output artifact kinds

Task execution goes through a `BackendSession` instance with:

- a backend name
- capability discovery
- task execution on resolved input artifacts

The current task vocabulary includes:

- `normalize`
- `factor`
- `reduce`
- `quotientRemainder`
- `groebnerBasis`
- `sumOfSquares`
- `eliminate`
- `solve`
- backend-specific extensions

Only a subset is implemented so far.

## Certificates and Discharge

The architecture makes a strict distinction between:

- certificate checking
- theorem closing / semantic discharge

Certificate checking validates backend output as a mathematical fact about artifacts already in the chain.

Dischargers consume checked judgments and derive new semantic judgments. For example:

- checked quotient-remainder with zero remainder
- derives ideal membership

This separation matters because different backends may share the same discharger once they return the same checked certificate shape.

## Current Implementation

### MRDI Layer

Implemented in:

- `MRDI/Basic.lean`
- `MRDI/Poly.lean`

Highlights:

- more faithful MRDI container handling
- reference-resolution support
- `MRDI.Poly`
- `MRDI.Ideal`

### Serialization

Implemented in:

- `Macaulean/Serialize.lean`

Highlights:

- polynomial serialization and deserialization for `Lean.Grind.CommRing.Poly`
- monomial-order normalization fix so transported certificates compare correctly

### CAS Semantics

Implemented in:

- `Macaulean/CAS/Semantics.lean`

Highlights:

- `ArtifactRef`
- `ArtifactKind`
- `Provenance`
- `Judgment`
- `Certificate`
- `Artifact`
- `StoredArtifact`

### Backend and Chain Layer

Implemented in:

- `Macaulean/CAS/Backend.lean`
- `Macaulean/CAS/Chain.lean`
- `Macaulean/CAS/Execution.lean`

Highlights:

- `TaskKind`
- `Capability`
- `TaskRequest`
- `TaskResult`
- `BackendSession`
- `ChainStep`
- `ChainState`

`ChainState` now records:

- raw backend judgments
- checked judgments
- derived judgments
- certificates

### Certificate Checkers

Implemented in:

- `Macaulean/CAS/Checkers.lean`

Current built-in certificate checkers:

- factorization certificates
- quotient-remainder certificates

The quotient-remainder checker reconstructs exact `Lean.Grind.CommRing.Poly` objects and verifies

`f = sum_i q_i * g_i + r`

inside Lean.

### Dischargers

Implemented in:

- `Macaulean/CAS/Dischargers.lean`

Current built-in discharger:

- zero remainder implies ideal membership

This is the first example of a theorem-closing step built on top of a checked backend certificate.

### Macaulay2 Backend

Implemented in:

- `Macaulean/Macaulay2.lean`
- `m2/macaulean.m2`
- `Macaulean/CAS/Macaulay2Backend.lean`

Implemented semantic tasks:

- exact factorization of naturals
- exact quotient-remainder for sparse commutative integer polynomials

Current public helper APIs on top of the backend:

- `factorNatUsingBackend`
- `quotientRemainderUsingBackend`
- `idealMembershipUsingBackend`

### User-Facing Vertical Slices

Implemented in:

- `Macaulean/Factorization.lean`
- `Macaulean/IdealMembership.lean`

Current theorem/tactic-facing slices:

- integer factorization through the checked backend path
- reducibility via checked factorization
- ideal membership for explicit generator lists via checked quotient-remainder and derived membership

The current ideal-membership frontend uses:

- `InIdeal`
- `linearCombination`
- `m2ideal_member`

The tactic reifies the goal polynomial and the explicit generator list, requests a checked quotient-remainder certificate from Macaulay2, uses the returned quotients as existential witnesses, and closes the final equality in Lean.

## Testing

The current branch has coverage at several levels.

### MRDI and Chain Tests

- `MacauleanTest/MRDI.lean`
- `MacauleanTest/CASChain.lean`

### Backend and Certificate Tests

- `MacauleanTest/CASBackend.lean`

This includes:

- capability advertisement
- certified factorization
- certified quotient-remainder
- derived ideal membership from zero remainder
- public quotient-remainder and ideal-membership helper APIs

### User-Facing Tests

- `MacauleanTest/Factorization.lean`
- `MacauleanTest/IdealMembership.lean`

The aggregate target is:

- `lake build MacauleanTest`

At the time of writing, that target passes on this branch except for the pre-existing warning in `MacauleanTest/Benchmarks.lean` caused by an existing `sorry`.

## What Is Still Missing

The branch has established the architecture and two end-to-end slices, but it is not finished.

The main missing pieces are:

- port sum-of-squares onto this backend/checker/discharger architecture
- add more certificate families beyond factorization and quotient-remainder
- enrich the MRDI profile with more explicit ambient/context objects
- add more theorem-facing frontends beyond explicit-list ideal membership
- generalize beyond the current exact sparse commutative polynomial slice

## Recommended Next Step

The most important next step is porting the sum-of-squares workflow onto this architecture.

That would exercise the full intended design:

- backend task
- exact certificate transport
- Lean certificate checker
- separate order-theoretic discharger
- thin user-facing tactic

At that point the branch would have both algebraic and ordered-certificate workflows using the same core execution model.
