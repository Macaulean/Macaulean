# June 2026 — Interim Report (Renaissance Philanthropy, AI for Math Fund)

**Project:** Bridging Proof and Computation: A Verified Lean–Macaulay2 Interface
**Project representative (per the RenPhil form):** Matthew Ballard — leykin@math.gatech.edu
**Reporting question:** *Progress Against Outputs and Outcomes — for each row in the
outputs-and-outcomes table from Section 4 (Impact) of the approved proposal,
describe progress to date.*

> The text below the line is the answer for the form's "Progress Against Outputs
> and Outcomes" box. It first states honestly where the project stands and what is
> demonstrable today, then walks the eight rows of the Section-4 table in order,
> quoting each Output/Outcome and describing progress as of June 2026. Claims are
> cross-referenced to the public repository (file paths, and the branch when a
> capability is not yet on `main`) and to the weekly meeting archive in
> [`../meetings/`](../meetings/), which was verified against the code.

---

## Where we stand (honest summary)

We are in the **first half** of the project (the proposal's milestones run through
Q2 2027; roughly 40% of the timeline has elapsed). Against the Section-4 table,
the two **Q1 2026** outputs (a Lean→Macaulay2 DSL and a structured translation
layer) and the **Q2 2026** output (certificate producing and handling) are
**delivered**, and we have begun work scheduled for **Q3–Q4 2026** and even the
exploratory **Q1 2027** Macaulay2-side proof-synthesis item.

Three concrete signals of real, working progress:

- **A non-trivial flagship is verified on the main line.** Lean checks, end-to-end
  through Macaulay2, that a Gröbner basis and the determinant of a 3×3 matrix of
  indeterminates lie in a **10-generator ideal in 9 variables** — a genuine
  commutative-algebra computation, not a toy
  (`MacauleanTest/TestGB5Pts.lean`, via the `m2idealmem` tactic + `grind`).
- **Part of the interface has been upstreamed into Macaulay2 itself.** The
  JSON-RPC and MRDI serialization packages are **now distributed with Macaulay2**
  rather than living only in our repository — durable impact beyond the project.
- **The architecture is already validated across three CAS backends** (Macaulay2,
  SymPy, Oscar/GAP) on the active development branches, which is the proposal's
  Q2 2027 "general framework" thesis demonstrated early.

**The one honest caveat, stated up front:** verification is *sound* but **not yet
cheap at scale**. The 9-variable flagship needs a raised kernel budget
(`maxHeartbeats 1000000`), and larger certificates (e.g. a ~3,700-monomial
identity) still exceed practical kernel limits. This is the proposal's own
emphasis on *efficient* verification, it is the single binding technical risk, and
it is where most current engineering is aimed (Row 4 and Risks).

Two structural facts shape everything below; we flag them because a careful reader
will compare against the approved plan (see "Deviations"):

1. **Backend-neutral by design.** A capability-driven backend interface over a
   backend-neutral format (MRDI, the Mathematical Research Data Initiative) lets
   multiple CAS plug in; this is already exercised by three backends.
2. **Two development fronts.** `main` holds a consolidated **core** (serialization,
   the `ConcretePoly` representation, the ideal-membership/factorization/remainder
   tactics, and the flagship example); the additional **breadth** — the SymPy and
   Oscar backends, Gröbner-reduction / radical / divisibility / sum-of-squares /
   `polyrith` / algebra-normalization tactics, and permutation-group membership —
   is implemented and tested on active feature branches and is being consolidated
   onto `main`. Where a capability below is branch-only, we say so.

A weekly working meeting (16 sessions recorded Nov 2025 – Jun 2026, full
transcripts in [`../meetings/`](../meetings/)) drives the work; core participants
are Matthew Ballard, Anton Leykin, Michael Stillman (Macaulay2 co-creator),
Damiano Testa, Jay Yang, and Douglas Torrance.

## Demonstrable results today

**On `main`:**
- **Ideal membership at real scale (flagship).** `MacauleanTest/TestGB5Pts.lean`
  proves, kernel-checked, that a Gröbner basis and the 3×3 determinant
  `e11 e22 e33 − …` lie in a 10-generator ideal in the 9 variables `e11…e33`. The
  `m2idealmem` tactic obtains the quotient–remainder certificate from Macaulay2,
  reduces the goal to polynomial identities, and `grind` closes them.
- **A compact, coefficient-parameterized polynomial representation** (`ConcretePoly`,
  in `Macaulean/IdealMembership.lean`) with MRDI serialization/deserialization
  (`toMrdi` / `fromMrdi?`) — the data structure that makes kernel checking
  tractable, and the mechanism for supporting coefficient rings beyond ℚ.
- **Working tactics:** `m2factor` / `m2reducible` (factorization & reducibility),
  `m2idealmem` and `m2remainder` (ideal membership / quotient–remainder), and the
  generic `macaulay` entry point, with a `grind` on/off config option.
- **Interface upstreamed:** the JSON-RPC and MRDI packages now ship with Macaulay2;
  `m2/macaulean.m2` and `m2/lean-mrdi.m2` hold the project-specific glue.

**On active branches (validated, consolidation pending):**
- **Three CAS backends behind one interface** — Macaulay2, SymPy, Oscar/GAP.
- **Six certificate-bearing strategies, each kernel-checked with no added axioms**
  (an early `native_decide` shortcut was removed in favor of kernel `decide`):
  ideal membership, Gröbner-basis reduction, radical membership (Rabinowitsch),
  polynomial divisibility, factorization, and permutation-group membership.
- **Kernel-verified permutation-group membership for A₅ (order 60, smallest
  non-abelian simple group), S₅, and D₄** via the Oscar/GAP backend — to our
  knowledge the first such CAS-backed tactic in Lean.

**Dissemination:** a contribution on the interface was **accepted for ICMS 2026
(Waterloo)**, with an **invited talk by Michael Stillman** — a peer-reviewed,
citable output.

---

## Progress against the Section-4 outputs and outcomes

### Row 1 — Q1 2026
**Output:** *Prototype Lean DSL for Macaulay2, enabling basic algebraic queries from Lean.*
**Outcome:** *Establishes the foundation for seamless interaction between theorem proving (Lean) and computational algebra (M2).*

**Delivered (on schedule), then deepened.** Lean tactics call Macaulay2 and use the
result inside a proof. The first slice was an integer reducibility/factorization
tactic (`factor_test`, demoed 2025-11-12; now `m2factor` / `m2reducible` on
`main`). On `main` this is now a working DSL of M2-backed tactics — `m2idealmem`
and `m2remainder` for ideal membership and quotient–remainder, plus the generic
`macaulay` entry point — built on Lean's core `grind` commutative-ring
representation rather than Mathlib, keeping the core small and auditable. (The CAS
branches add a capability-dispatching `cas` entry point over additional backends.)
The "foundation for seamless interaction" is met: an end-to-end Lean→M2→Lean path
exists and is exercised by tests, up to the 9-variable flagship.
*Evidence (on `main`):* `Macaulean/Factorization.lean`,
`Macaulean/IdealMembership.lean`, `Main.lean`; meetings 2025-11-12, 2025-11-19.

### Row 2 — Q1 2026
**Output:** *Parser to translate Lean expressions into Macaulay2 commands and return structured results.*
**Outcome:** *Provides an initial framework for future CAS-theorem prover integrations.*

**Delivered as a structured interchange — and partly upstreamed into Macaulay2.** A
proposal risk was that fragile string parsing would make communication unreliable;
we avoided it with a structured, backend-neutral format (**MRDI**) carried over
**JSON-RPC**. Lean reifies a goal into its `grind` ring representation, serializes
objects to MRDI (`toMrdi` / `fromMrdi?`, UUID-identified, via `ConcretePoly`),
sends them to Macaulay2, and deserializes structured results back into Lean;
round-tripping is exercised by `MacauleanTest/Poly.lean`. A notable outcome this
period: the **JSON-RPC and MRDI packages are now distributed with Macaulay2
itself** (they were removed from our repo as standalone copies), so the transport
and data layers are reusable by anyone, not just this project — concrete evidence
that this is a "framework for future CAS-theorem prover integrations." The
project-specific glue remains in `m2/macaulean.m2` and `m2/lean-mrdi.m2`.
*Evidence (on `main`):* `MRDI/Basic.lean`, `MRDI/Poly.lean`, `MRDI/Uuid.lean`,
`Macaulean/Serialize.lean`, `m2/macaulean.m2`, `m2/lean-mrdi.m2`;
meetings 2025-11-19, 2025-12-03, 2026-02-03, 2026-04-07.

### Row 3 — Q2 2026
**Output:** *Implementations of certificate producing and handling.*
**Outcome:** *Allows Macaulay2 computations to be formally verified inside Lean, ensuring trust in computational results.*

**Delivered (on schedule).** Macaulay2 returns explicit **certificates** that Lean
re-checks. The core, on `main`, is the quotient–remainder certificate for ideal
membership: Macaulay2 returns cofactors (as `ConcretePoly` quotients and a
remainder); Lean rebuilds the polynomials, confirms the remainder vanishes, and
reduces the goal to polynomial identities that are then discharged — the basis of
the 9-variable flagship. On the development branches this generalizes to **six
certificate types, all kernel-checked with no added axioms** (factorization, ideal
membership/quotient–remainder, Gröbner-basis reduction, radical membership,
polynomial divisibility, permutation-group membership), with certificate *checking*
kept separate from theorem *closing* so a checker is reusable across backends. The
"formally verified inside Lean, ensuring trust" outcome holds: the CAS is never
trusted; only the Lean kernel and the in-Lean checkers are.
*Evidence:* `Macaulean/IdealMembership.lean`, `MacauleanTest/TestGB5Pts.lean`
(on `main`); the broader strategy set and `CAS_ARCHITECTURE.md` on the CAS branches
(`cas-design`, `groebner-tactic`); meetings 2026-01-13, 2026-02-03, 2026-03-03.

### Row 4 — Q3 2026
**Output:** *Develop efficient proof tactics in Lean to handle computational algebra results.*
**Outcome:** *Provides reusable tools for verifying CAS computations in theorem proving.*

**On track on breadth; efficiency is the current frontier (and the project's main
risk).** A reusable suite already exists: on `main`, `m2idealmem`, `m2remainder`,
`m2factor`/`m2reducible`; on branches, Gröbner-basis reduction (`gb_reduce`),
sum-of-squares (`m2sos`), a `polyrith`-style certificate tactic (`m2polyrith`), a
reflective algebra-normalizer (`algebra_norm`, on a from-scratch two-level
`AlgPoly` type), and radical-membership / divisibility / permutation-group
strategies. The operative word is **efficient**: large certificates stress the
kernel (polynomial multiplication, large coefficients, recursion depth). The key
mitigation is on `main` already — the compact `ConcretePoly` representation, which
mirrors Macaulay2's term structure and is **parameterized over its coefficient
ring** (the mechanism for moving beyond ℚ; see Deviations). The 9-variable
flagship verifies with a raised heartbeat budget; pushing to substantially larger
certificates is the open Q3 work (explored ideas: sorted term-lists, monomial
reordering, geo-buckets, syzygy/GrevLex-shortened certificates, straight-line
programs).
*Evidence:* `Macaulean/IdealMembership.lean` (`ConcretePoly`),
`MacauleanTest/TestGB5Pts.lean` (on `main`); `Macaulean/Grind/AlgPoly/*.lean`, the
`polyrith` branch; meetings 2026-03-03, 2026-03-17, 2026-03-24, 2026-04-21,
2026-05-26.

### Row 5 — Q4 2026
**Output:** *Macaulay2 package dedicated to the Lean interface. Implementation of necessary data structures and methods.*
**Outcome:** *Provides a convenient interface for a Macaulay2 user to interact with Lean pursuing a goal of producing formal proofs of computational results.*

**Ahead of schedule; the strongest single piece is already upstreamed.** The
Macaulay2 side implements the interface and exposes semantic methods — a
request/response main loop, ideal membership returning quotient–remainder
certificates as `ConcretePoly` objects, factorization, sum-of-squares, and
`toLean`/`fromLean` conversions (`m2/macaulean.m2`), plus M2 classes mirroring Lean
polynomial objects (`m2/lean-mrdi.m2`) and MRDI validation (`m2/validate-mrdi.m2`).
Crucially, the **JSON-RPC and MRDI packages have been upstreamed into the Macaulay2
distribution**, so a Macaulay2 user already gets the serialization/transport layer
for free. New work this period also includes an AI-assisted stored-artifact
prototype (M2 writes results to files that proofs reference) and a June prototype
that decomposes a CAS problem into atomic polynomial-identity tasks for Lean.
Remaining to fully close this Q4 row: packaging the project-specific glue as a
registered, installable Macaulay2 package.
*Evidence (on `main`):* `m2/macaulean.m2`, `m2/lean-mrdi.m2`,
`m2/validate-mrdi.m2`; meetings 2026-03-31, 2026-04-07, 2026-04-28, 2026-06-02.

### Row 6 — Q4 2026
**Output:** *Implementation of Lean tactics to invoke Macaulay2 computations within proofs.*
**Outcome:** *Enables theorem proving workflows where AI-assisted proof generation can seamlessly incorporate CAS calculations.*

**Core capability achieved early.** Tactics that invoke Macaulay2 *within* a proof
and discharge the goal from the checked result work end-to-end on `main` (ideal
membership, factorization, remainder), demonstrated up to the 9-variable flagship.
The outcome's distinctive clause — *AI-assisted proof generation incorporating
CAS* — is shown most clearly by an episode in which an AI assistant drove
Macaulay2's sum-of-squares package over JSON-RPC to build the `m2sos` tactic live
(2026-02-10). Separately, as a development practice, AI coding assistants (Claude,
Codex) co-authored a substantial share of the implementation — about a quarter of
commits in the most recently reported quarter (27 of 108, per `Reports/2026_03.md`).
We distinguish the two: the former evidences the outcome; the latter is how we work.
*Evidence (on `main`):* `Macaulean/IdealMembership.lean`,
`MacauleanTest/TestGB5Pts.lean`; meetings 2026-02-10, 2026-03-31; `Reports/2026_03.md`.

### Row 7 — Q1 2027
**Output:** *Investigate theorem prover interfaces within Macaulay2, in particular proof synthesis.*
**Outcome:** *Bridges the gap between symbolic computation and formal mathematics by allowing CAS-generated results to be directly formalized.*

**Started early (this is a Q1 2027 item).** We have begun investigating
Macaulay2-side proof synthesis: a June prototype in which Macaulay2 decomposes a
computation (ideal membership, exhibiting a Gröbner basis, computing a dimension)
into a list of **atomic polynomial-identity tasks** plus a meta-theorem asserting
their equivalence to the original statement, then ships those tasks to Lean to be
discharged. Related ideas under active discussion: having M2 *log* its internal
operations so Lean can reconstruct proof terms, and the stored-artifact pathway
above. This is the "CAS-generated results directly formalized" direction, begun
ahead of its scheduled quarter — though still exploratory.
*Evidence:* meetings 2026-03-31, 2026-04-07, 2026-04-21, 2026-06-02.

### Row 8 — Q2 2027
**Output:** *Publish framework for a general CAS-theorem prover integration model.*
**Outcome:** *Establishes a blueprint for connecting theorem provers with CAS beyond Macaulay2.*

**On track; the generalization is already demonstrated, and dissemination has
begun.** The architecture is a CAS-agnostic model (capability-advertising backends,
MRDI interchange, a strict certificate-checking / theorem-closing separation), and
the generalization claim is **shown, not asserted**: on the development branches,
beyond Macaulay2 we added a **SymPy** backend (Gröbner bases, factorization,
radical membership) and an **Oscar/Julia** backend (permutation-group membership
via GAP), each plugging into the same core. Dissemination: a contribution on the
Lean–Macaulay2 interface was **accepted for ICMS 2026 (Waterloo)** (with an invited
talk by Michael Stillman); the design is documented in `CAS_ARCHITECTURE.md` (CAS
branches); and the MRDI/JSON-RPC layer is now shipped with Macaulay2. Formal
publication of the general framework remains the Q2 2027 target.
*Evidence:* `Macaulean/SymPy.lean`, `Macaulean/Oscar.lean`,
`Macaulean/PermGroup.lean`, `sympy/macaulean_sympy.py`, `oscar/macaulean_oscar.jl`,
`CAS_ARCHITECTURE.md` (CAS branches); meetings 2026-03-17, 2026-04-07, 2026-04-14.

---

## Status vs. the approved proposal: deviations and mitigations

We flag these proactively because a careful reader will compare against the
approved plan.

- **Mathlib alignment → core `grind` instead.** The proposal anticipated building
  on Mathlib's algebraic hierarchy. We found that wrapping Mathlib's `MvPolynomial`
  is hostile to kernel-level verification and instead built on Lean's core `grind`
  representation behind an implementation-agnostic interface — a smaller, faster,
  more auditable core. Path back to the proposal's intent: a Mathlib-facing layer
  can sit on top without disturbing the core.
- **Core on `main` vs. breadth on branches.** The three backends, the six-strategy
  set, the AlgPoly normalizer, and permutation-group membership are validated on
  active branches rather than `main`. Consolidating them onto `main` is in
  progress; the capabilities are real and tested where they live. This is a
  sequencing choice, not abandoned work.
- **Coefficient generality (ℤ/p, char-p).** Strongest over ℚ/ℤ today; the
  `ConcretePoly` representation is parameterized over its coefficient ring, which
  is the structural mechanism now in place for ℤ/p and richer coefficients.
- **Macaulay2 package.** Strong here: the JSON-RPC + MRDI layers are upstreamed
  into Macaulay2. Registering the remaining project-specific glue as an installable
  package is the open step for the Q4 2026 row.

## By the numbers (verified against the repo)

- **6** core participants — **5** contributing code (Yang, Ballard, Torrance,
  Testa, Leykin) plus Macaulay2 co-creator **Michael Stillman** (collaborator).
- **3** CAS backends behind one interface (Macaulay2, SymPy, Oscar/GAP) — on the
  development branches.
- **6** certificate-bearing strategies, **0** added axioms (kernel `decide`).
- Flagship verified on `main`: a **10-generator ideal in 9 variables**
  (`MacauleanTest/TestGB5Pts.lean`).
- Part of the interface (**JSON-RPC + MRDI**) **now distributed with Macaulay2**.
- **16** recorded weekly meetings (Nov 2025 – Jun 2026), full transcripts in
  [`../meetings/`](../meetings/).

## Engagement and dissemination

- **ICMS 2026 (Waterloo):** contribution **accepted**; **invited talk** by Michael
  Stillman.
- **Completed:** MARC workshop at Clemson (April 2026; talk by Julia Lindberg).
- **Upcoming:** the **AI for Math** event in **London, Sep 17–18, 2026**; Georgia
  Tech / Macaulay2 visits.
- **External interest / collaboration:** a UK group formalizing the **LMFDB** has
  expressed interest in our polynomial-verification work (interest at this stage);
  we are in **active talks with the Mathlib Initiative** — newly funded (Alex
  Gerko/XTX; a Sloan Foundation gift specifically to expand Mathlib's
  *computational* capabilities) and itself within Renaissance Philanthropy's
  Lean/Mathlib orbit — about collaboration and shared hiring.

## Risks and where support is most useful

- **Kernel verification performance is the dominant risk** and the main current
  focus. Mitigation in progress: the compact `ConcretePoly` representation and the
  atomic-task decomposition. Upstream Lean improvements to recursion-depth and
  large-term handling would directly unlock larger instances; engagement with the
  Lean core team / Mathlib Initiative on this is valuable.
- **Coefficient generality** beyond ℚ/ℤ is being addressed via the
  coefficient-parameterized representation; ℤ/p is the next target.
- **Consolidation and packaging** (merging the branch breadth onto `main`;
  registering an installable Macaulay2 package) are near-term engineering steps,
  not research risks.
