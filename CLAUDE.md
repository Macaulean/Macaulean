# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Macaulean is a Lean 4 interface to [Macaulay2](https://github.com/Macaulay2/M2/wiki) (a computer algebra system). It provides Lean tactics that offload polynomial computations to Macaulay2 via JSON-RPC, then reconstruct formal proofs in Lean. Key tactics: `m2factor` (integer factorization), `m2reducible` (prove non-irreducibility), and `m2idealmem` (ideal membership).

## Build Commands

```bash
lake build macaulean       # Build the main executable
lake build MacauleanTest   # Build and run all tests
lake build Macaulean       # Build only the library
lake build MRDI            # Build only the MRDI library
```

Lean version: v4.26.0-rc1 (specified in `lean-toolchain`). Build system is Lake, configured in `lakefile.toml`.

## Prerequisites

Macaulay2 must be installed on the system. The M2 server is spawned as a child process by `startM2Server()` using the script at `m2/macaulean.m2`.

## Architecture

### Communication Flow

```
Lean Tactics → MRDI Serialization → JSON-RPC Client → M2 Server (child process)
                                                           ↓
Lean Proofs  ← MRDI Deserialization ← JSON-RPC Response ← M2 Computation
```

JSON-RPC uses LSP-style `Content-Length` framing over stdio.

### Lean Libraries

- **`Macaulean/`** — Core library
  - `Macaulay2.lean` — JSON-RPC client: spawns M2 process, sends requests, receives responses. `globalM2Server` holds the singleton server reference.
  - `Factorization.lean` — `m2factor` and `m2reducible` tactics. Calls `factorNat()`, then constructs proof terms.
  - `IdealMembership.lean` — `m2idealmem` tactic. Serializes polynomials as `ConcretePoly`, calls `quotientRemainder`, reconstructs proof from quotients.
  - `Serialize.lean` — Serialization utilities.

- **`MRDI/`** — [MRDI format](https://arxiv.org/abs/2309.00465) implementation (Macaulay2 Readable/Writable Data Interchange)
  - `Basic.lean` — Core types (`MrdiState`, `MrdiT` state monad, `MrdiEncodeT`/`MrdiDecodeT`), `MrdiType` typeclass with `encode`/`decode?`.
  - `Poly.lean` — Bidirectional conversion between `Grind.CommRing.Poly` and MRDI format.
  - `Uuid.lean` — RFC 4122 UUID generation and parsing (`BitVec 128`).

- **`MacauleanTest/`** — Tests using `#guard_msgs` and `#eval` directives.

### Macaulay2 Backend (`m2/`)

- `macaulean.m2` — Server entry point; loads packages, registers methods, runs main loop.
- `JSONRPC.m2` — JSON-RPC 2.0 server implementation.
- `MRDI.m2` — MRDI serialization/deserialization for M2 objects.
- `lean-mrdi.m2` — Lean-specific types (`LeanGrindCommRingPoly`, `ConcretePoly`) and their MRDI conversions.

### Key M2 Methods

| Method | Purpose | Input/Output |
|--------|---------|-------------|
| `quotientRemainder` | Ideal membership | MRDI `ConcretePoly` → quotient polynomials |
| `factorInt` | Integer factorization | Integer → `[[prime, exp], ...]` |

### Polynomial Representation

Lean uses `Grind.CommRing.Poly` (recursive: `Poly.num k` for constants, `Poly.add k m p` for `k*m + p`). `ConcretePoly R` wraps this with concrete ring element coefficients. MRDI format uses arrays of terms with coefficient/monomial pairs.

### Monad Stack

MRDI operations use layered state monads: `MrdiT` (base state for UUID generation and object storage) → `MrdiEncodeT` (adds reference tracking) / `MrdiDecodeT` (adds reference lookup via `ReaderT`). `runMrdiWithSeed` enables deterministic UUIDs for testing.
