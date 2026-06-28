# Weekly meeting archive — "Lean M2 meeting"

Exported Zoom recordings of the project's weekly working/coordination meeting
(Zoom meeting ID 837 1010 5166, host account `sc-edu.zoom.us`, timezone
America/New_York). Each dated file contains the Zoom AI **summary**, the
**topic breakdown**, the **action items**, the **attendee list**, and the
**full transcript** of that meeting.

These are the source record behind the progress described in
[`../Reports/2026_06_interim.md`](../Reports/2026_06_interim.md).

Recording of the series begins mid-November 2025; earlier kickoff meetings in
October–early November 2025 were not recorded to the cloud. 16 sessions are
archived here, spanning 2025-11-12 → 2026-06-02.

| Date | Approx. length | Focus (one line) |
|------|----------------|------------------|
| [2025-11-12](2025-11-12.md) | ~67 min | M2 server process (`IRef`), `factor_test` (naturals reducible via M2), MRDI-vs-JSON-RPC serialization debate, tactic-syntax design, `grind` over ℤ |
| [2025-11-19](2025-11-19.md) | ~76 min | Group coding: polynomial/monomial serialization to an M2-compatible JSON format (coeff-before-powers, non-zero terms); irreducibility-via-Sage-certificate tactic |
| [2025-12-03](2025-12-03.md) | ~80 min | MRDI plumbing for integer-coefficient polynomials; round-trip echo test + `fromMerdi`; UUIDs; M2 error-handling PR; trust/`sorry`/warning discussion |
| [2026-01-13](2026-01-13.md) | ~66 min | Lean-expr → `grind` CommRing expr → poly pipeline; ideal membership via Gröbner basis + mod-primes equality; M2 to emit a certificate in MRDI; Ideal Membership + Benchmarks branches |
| [2026-02-03](2026-02-03.md) | ~51 min | MRDI serialize/deserialize integrated in `Poly.lean`; `MerdiEncode`/`MerdiDecode` monads; M2 ideal-membership cofactor certificate; AI-tooling demo |
| [2026-02-10](2026-02-10.md) | ~60 min | Live-built sum-of-squares tactic calling M2's M2SOS over JSON-RPC; inductive SOS predicate; weighted-SOS-over-ℚ caveats; certificate-verification intent; M2 IO/parser blockers |
| [2026-03-03](2026-03-03.md) | ~42 min | Certificate-size bottleneck (G ≈ 4,000 terms, GB intermediate ≈ 100k); quotient-remainder framing of ideal membership; kernel deep-recursion; concrete test `1 ∈ (x²+y²−1, 2x, 2y)`; char-p universalization |
| [2026-03-17](2026-03-17.md) | ~53 min | Polynomial-reordering tactic; `grind`-based polynomial type with `denote`/reification; Mathlib Gröbner bases are definitional only; implementation-agnostic typeclass interface; ICMS abstract |
| [2026-03-24](2026-03-24.md) | ~72 min | Serialization with sorted term-lists (ℤ/Nat fallback, negative-coeff fix); `grind` needs fields; kernel perf — polynomial multiplication as the key bottleneck; `conv` mode |
| [2026-03-31](2026-03-31.md) | ~68 min | Reusable CAS components; "stored artifact" feature (M2 saves results to files, referenced in proofs); Sage-as-backend certificates; ideal-membership branch merge; summer intern |
| [2026-04-07](2026-04-07.md) | ~62 min | Decision to build a bespoke polynomial type; `polyrith` denotable lazy poly type; ideal-membership merged to main + `±` config syntax (grind/GB); MRDI/RPC overview write-up |
| [2026-04-14](2026-04-14.md) | ~54 min | Mirroring M2's internal data structures (non-recursive); `native_decide` axiom transparency; LMFDB (UK) group interest in polynomial verification; ICMS/MARC/UK/ICARM events |
| [2026-04-21](2026-04-21.md) | ~60 min | Single-file MRDI (problem + certificate); monomial exponent-vector encodings; `native_decide` axiom granularity; quotient-type tradeoffs; compact `PolyRep` (~80%); AI-for-Math London event |
| [2026-04-28](2026-04-28.md) | ~62 min | Compact certificate representations (Waring, subalgebra, straight-line programs); numerical certification via interval arithmetic; monomial-as-list refactor; MRDI serialization scope |
| [2026-05-26](2026-05-26.md) | ~64 min | Working Lean↔M2 channel for small cases; 3,725-monomial certificate benchmark; syzygies + GrevLex for shorter certificates; new poly representation nearly `sorry`-free; simp/simproc work; Mathlib Initiative funding |
| [2026-06-02](2026-06-02.md) | ~28 min | M2 prototyping framework reducing problems (ideal membership, Gröbner basis, dimension) to atomic polynomial identities Lean verifies; meta-theorem decomposition; hiring/scheduling |

**Recurring participants:** Matthew Ballard, Anton Leykin, Michael Stillman,
Damiano Testa, Jay Yang, Douglas Torrance.

> Note: the 2026-06-02 recording has no Zoom-generated word-for-word transcript
> (no caption/VTT asset was produced); that file's summary, topics, and action
> items are complete, but its Transcript section contains only the short "My
> Notes" fragment that exists.
