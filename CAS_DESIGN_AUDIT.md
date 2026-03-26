# CAS Design Audit

This document records an audit of the Lean-to-CAS integration design as of 2026-03-26, on the `cas-sos-refactor` branch (commit be5117e).

It covers alignment between planning documents and the implementation, architectural strengths, and open concerns.

## Original Vision vs. Current State

`Conversion_ideas.md` lists four initial conversions:

| Planned | Status |
|---------|--------|
| Integer -> Factorization | Done (certified) |
| Polynomial -> Factorization | **Not implemented** |
| Ideal -> Groebner basis | Not directly exposed (used internally by quotient-remainder) |
| (Ideal, polynomial) -> Membership certificate | Done (certified, via quotient-remainder + discharger) |

Beyond the original scope, the project has also shipped **SOS certificates** (sum-of-squares for nonnegativity) and **generic ambient field support** (`Algebra Rat A`).

## Architecture Strengths

### 1. Trust model is correctly designed and implemented

The invariant -- CAS never directly produces Lean proof terms -- is enforced at every level. Every path from M2 to a closed goal passes through:

- A certificate checker that re-derives the mathematical identity purely in Lean (`Checkers.lean`)
- A discharger that produces semantic judgments from checked certificates (`Dischargers.lean`)
- A tactic that builds a kernel-verifiable proof term

The kernel never trusts M2.

### 2. Clean layer separation

The four-layer split (MRDI -> Semantics -> Execution -> Tactics) means:

- New backends can be added via `BackendSession` instances without touching checker/discharger code
- New certificate families only require a checker + discharger, not changes to execution
- Tactics remain thin wrappers over checked judgments

### 3. Chaining model is sound

`ChainState` tracks the distinction between raw judgments, checked judgments, and derived judgments. The execution pipeline (`Execution.lean:21-49`) enforces the order: resolve -> backend call -> record -> check -> discharge. This prevents accidentally using unchecked backend claims.

### 4. M2-side self-verification

The M2 SOS handler (`macaulean.m2:74-80`) does its own sanity check (`lhs =!= rhs`) before returning. This is defense-in-depth -- Lean will verify independently, but catching errors early in M2 is good engineering.

### 5. Two-level normalization for generic ambient fields

The AlgPoly infrastructure separates coefficient arithmetic (over R, handled by `Lean.Grind.CommRing.Poly`) from ambient structure (over A, handled by `AlgPoly`). This is what enables SOS to work over any `Field A` with `Algebra Rat A`.

## Design Concerns

### 1. `Conversion_ideas.md` is stale

It does not reflect the current scope (SOS, generic ambient fields, the CAS architecture itself). The questions it raises ("Coefficients TBD", "Ambient ring TBD") have been answered by the implementation. Consider either updating it or removing it in favor of `CAS_ARCHITECTURE.md`, which is comprehensive and accurate.

### 2. Polynomial factorization is still missing

The original ideas doc lists it, `CAS_ARCHITECTURE.md` acknowledges it indirectly under "What Is Still Missing" (via "generalize beyond the current exact sparse commutative polynomial slice"), but there is no explicit plan for it. M2 can easily factor polynomials -- the gap is on the Lean certificate-checking side (how to represent and verify irreducibility or factorization of polynomials, which is harder than for integers).

### 3. Groebner basis as a first-class artifact

Currently GB computation is implicit inside `quotientRemainder`. The `TaskKind.groebnerBasis` variant exists in the enum but is not implemented. Exposing it directly would enable:

- Caching a GB across multiple membership queries against the same ideal
- Multi-step chains where a GB feeds into elimination or solving
- Direct user access to GB certificates

### 4. Checker/discharger registries are static arrays

`builtinCertificateCheckers` and `builtinJudgmentDischargers` in `Checkers.lean` and `Dischargers.lean` are hardcoded arrays. This works fine now with three checkers, but the architecture doc implies extensibility. An `Environment`-based registration (like Lean's attribute system) would scale better as certificate families grow.

### 5. Artifact IDs are not cryptographically meaningful

`ArtifactRef` IDs are strings like `"m2:factor:3"` -- sequential counters. This is fine for single-session use, but if chains are ever persisted or replayed across sessions, or multiple backends run concurrently, true UUIDs or session-scoped namespacing would be needed. Low priority given current usage.

### 6. Capability advertisement is declared but not queried

The `BackendSession.capabilities` method exists and M2 declares its capabilities, but `executeStep` never checks whether the backend actually supports the requested task before calling `runTask`. It just dispatches and gets `.unsupported` back. Pre-checking would give better error messages and enable task routing when multiple backends exist.

### 7. M2 process lifecycle is fragile

`Macaulay2Session.stop` is a no-op. The M2 process is spawned but never explicitly killed. The global singleton pattern (`globalM2Server` / `globalMacaulay2Session`) means:

- If M2 crashes mid-session, there is no recovery or restart
- Multiple concurrent tactic invocations share one M2 process with sequential JSON-RPC (no multiplexing)
- No timeout on M2 calls -- a hanging SDP solver blocks the Lean elaborator indefinitely

### 8. MRDI profile lacks ambient context

`CAS_ARCHITECTURE.md` explicitly flags this as the biggest missing piece. Polynomial payloads carry coefficient data and monomials but do not encode what ring they live in, what the variable names mean, or what monomial order is in use. The `PolynomialRingContext` structure exists in `Semantics.lean:29-33` but is not used anywhere yet. This matters once chains involve steps whose output feeds another step over a different ring.

### 9. `unsafe` in the tactic layer

Several functions in `SumOfSquares.lean` and `Tactic.lean` are marked `unsafe` (for `evalExpr` and similar). This is standard for Lean metaprogramming but worth tracking -- these are the points where a bug could produce an incorrect proof term that the kernel would reject at `#check` time. The `unsafe` boundary is small and well-contained.

### 10. M2-side JSON parsing is acknowledged as inefficient

The `getc`-based character-by-character parser (comment on `macaulean.m2` line 111) works for current polynomial sizes but will become a bottleneck for large payloads (big Groebner bases, high-degree SOS decompositions).

## Document Alignment

| `Conversion_ideas.md` | `CAS_ARCHITECTURE.md` | Implementation |
|---|---|---|
| Integer factorization | Documented as implemented | Done |
| Polynomial factorization | Mentioned in task vocabulary, not in "Current Implementation" | Missing |
| Groebner basis | In task vocabulary, not implemented | Missing |
| Ideal membership | Documented as implemented | Done |
| -- | SOS certificates | Done |
| -- | Generic ambient fields | Done (be5117e) |

## Recommended Priorities

1. **Update or retire `Conversion_ideas.md`** -- it no longer reflects the project scope
2. **Polynomial factorization** -- this is the original-scope item with the most remaining design work (certificate format for polynomial irreducibility)
3. **Wire up `PolynomialRingContext`** -- the structure exists but is dead code; connecting it to artifact payloads would unblock multi-ring chains
4. **M2 process robustness** -- timeout support and crash recovery would make the tool usable in interactive editing without fear of hangs
