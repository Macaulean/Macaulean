# June 2026 — Interim Report (Renaissance Philanthropy, AI for Math Fund)

**Project:** Bridging Proof and Computation: A Verified Lean–Macaulay2 Interface
**Principal investigators:** Matthew Ballard (Lean side) and Anton Leykin (Macaulay2 side, leykin@math.gatech.edu)
**Reporting question:** *Progress Against Outputs and Outcomes — for each row in the
outputs-and-outcomes table from Section 4 (Impact) of the approved proposal,
describe progress to date.*

> The text below the line answers the form's "Progress Against Outputs and
> Outcomes" box. It states where the project stands and what is demonstrable
> today, then walks the eight rows of the Section-4 table in order, quoting each
> Output/Outcome and describing progress as of June 2026. Claims are
> cross-referenced to the public repository (file paths, with the branch noted
> when a capability is not yet on `main`).

---

## Where we stand

We are at roughly the 40% mark of a plan that runs through Q2 2027. The honest
one-line summary: **the conceptual design work is largely behind us, and we are
now in implementation.** Against the Section-4 table, the two **Q1 2026** outputs
(a Lean→Macaulay2 DSL and a structured translation layer) and the **Q2 2026**
output (certificate producing and handling) are delivered; we have started work
scheduled for **Q3–Q4 2026** and even the exploratory **Q1 2027**
Macaulay2-side proof-synthesis item.

Three concrete signals of working progress:

- **The full Lean→Macaulay2→Lean path runs end-to-end on a non-trivial problem.**
  Lean checks, through Macaulay2, that a Gröbner basis and the determinant of a 3×3
  matrix of indeterminates lie in a **10-generator ideal in 9 variables** — a smoke
  test that exercises the whole pipeline on real input, on the way to genuine
  mathematical use (`MacauleanTest/TestGB5Pts.lean`, via the `m2idealmem` tactic +
  `grind`).
- **Part of the interface has been upstreamed into Macaulay2 itself.** The
  JSON-RPC and MRDI packages now ship with the Macaulay2 distribution rather than
  living only in our repository — durable impact that outlasts the grant and is
  reusable by anyone, not just this project.
- **The architecture has been validated across three CAS backends** (Macaulay2,
  SymPy, Oscar/GAP) on the active development branches — the proposal's Q2 2027
  "general framework" thesis demonstrated early.

**The honest caveat, stated up front:** verification is *sound* but **not yet
cheap at scale**. The 9-variable example needs a raised kernel budget
(`maxHeartbeats 1000000`), and larger certificates (e.g. a ~3,700-monomial
identity) still exceed practical kernel limits. This is the proposal's own
emphasis on *efficient* verification; it is the single binding technical risk and
where most current engineering is aimed (Row 4 and Risks).

Two design choices, refined over the first half and now driving implementation,
shape everything below:

1. **Backend-neutral, with a clean separation between the CAS round-trip and the
   final proof step.** The conceptual refinement this period was to stop thinking
   of "the tactic" as one monolithic hammer that must end in a kernel-checked
   `grind`, and instead split it: Macaulay2 produces a certificate, Lean reduces
   the goal to concrete polynomial identities, and *how those identities are
   discharged* becomes a pluggable choice. The default and strongest setting is a
   kernel re-check (the CAS is an untrusted oracle; trust lives in the Lean
   kernel). But the same machinery lets a user supply their own discharger, finish
   by a cheaper route (coefficient comparison, modular sampling), or simply take
   the reduced goal back and proceed by hand — and, where they choose, accept
   Macaulay2's computation at a trust level they set. This modularity widens the
   set of problems we can usefully serve and is the main direction of current work.
2. **A consolidated core, with breadth proven on branches.** `main` holds the
   core (serialization, the `ConcretePoly` representation, the
   ideal-membership/factorization/remainder tactics, the end-to-end smoke-test
   example); the
   additional breadth — SymPy and Oscar backends, Gröbner-reduction / radical /
   divisibility / sum-of-squares / `polyrith` / algebra-normalization strategies,
   and permutation-group membership — is implemented and tested on active feature
   branches and is being consolidated onto `main`. Where a capability below is
   branch-only, we say so.

## Demonstrable results today

**On `main`:**
- **Ideal membership, full path end to end.** `MacauleanTest/TestGB5Pts.lean` proves,
  kernel-checked, that a Gröbner basis and the 3×3 determinant
  `e11 e22 e33 − …` lie in a 10-generator ideal in the 9 variables `e11…e33`. The
  `m2idealmem` tactic obtains the quotient–remainder certificate from Macaulay2,
  reduces the goal to polynomial identities, and `grind` closes them.
- **A compact, coefficient-parameterized polynomial representation**
  (`ConcretePoly`, in `Macaulean/IdealMembership.lean`) with MRDI
  serialization/deserialization (`toMrdi` / `fromMrdi?`) — the data structure that
  makes kernel checking tractable and the mechanism for supporting coefficient
  rings beyond ℚ.
- **Working tactics:** `m2factor` / `m2reducible` (factorization & reducibility),
  `m2idealmem` and `m2remainder` (ideal membership / quotient–remainder), and the
  generic `macaulay` entry point, with a config option to run `grind` or hand the
  reduced goal back.
- **Interface upstreamed:** the JSON-RPC and MRDI packages now ship with Macaulay2;
  the remaining project-specific glue lives in `m2/` (`macaulean.m2`, `lean-mrdi.m2`).

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

**Delivered on schedule, then deepened.** Lean tactics call Macaulay2 and use the
result inside a proof. The first slice was an integer reducibility/factorization
tactic (now `m2factor` / `m2reducible` on `main`). On `main` this is now a working
DSL of M2-backed tactics — `m2idealmem` and `m2remainder` for ideal membership and
quotient–remainder, plus the generic `macaulay` entry point — built on Lean's core
`grind` commutative-ring representation rather than Mathlib, which keeps the core
small and auditable. (The CAS branches add a capability-dispatching `cas` entry
point over additional backends.) The "foundation for seamless interaction" is met:
an end-to-end Lean→M2→Lean path exists and is exercised by tests, up to the
9-variable example.
*Evidence (on `main`):* `Macaulean/Factorization.lean`,
`Macaulean/IdealMembership.lean`, `Main.lean`.

### Row 2 — Q1 2026
**Output:** *Parser to translate Lean expressions into Macaulay2 commands and return structured results.*
**Outcome:** *Provides an initial framework for future CAS-theorem prover integrations.*

**Delivered as a structured interchange — and partly upstreamed into Macaulay2.** A
proposal risk was that fragile string parsing would make communication unreliable;
we avoided it with a structured, backend-neutral format (**MRDI**, the Mathematical
Research Data Initiative) carried over **JSON-RPC**. Lean reifies a goal into its
`grind` ring representation, serializes objects to MRDI (`toMrdi` / `fromMrdi?`,
UUID-identified, via `ConcretePoly`), sends them to Macaulay2, and deserializes
structured results back into Lean; round-tripping is exercised by
`MacauleanTest/Poly.lean`. The payoff of committing to a *standard* serialization
format rather than ad-hoc strings is larger than it looks: it is what let the
**JSON-RPC and MRDI packages be upstreamed into Macaulay2 itself** this period (they
were removed from our repo as standalone copies), so the transport and data layers
are now reusable by anyone — concrete evidence of a "framework for future
CAS-theorem prover integrations." The same standard format also underpins a
saved-state pathway: results serialized to MRDI can be written to disk and a proof
restored from that stored artifact rather than recomputed (Row 5). The
project-specific glue remains in `m2/macaulean.m2` and `m2/lean-mrdi.m2`.
*Evidence (on `main`):* `MRDI/Basic.lean`, `MRDI/Poly.lean`, `MRDI/Uuid.lean`,
`Macaulean/Serialize.lean`, `m2/macaulean.m2`, `m2/lean-mrdi.m2`.

### Row 3 — Q2 2026
**Output:** *Implementations of certificate producing and handling.*
**Outcome:** *Allows Macaulay2 computations to be formally verified inside Lean, ensuring trust in computational results.*

**Delivered on schedule.** Macaulay2 returns explicit **certificates** that Lean
re-checks. The core, on `main`, is the quotient–remainder certificate for ideal
membership: Macaulay2 returns cofactors (as `ConcretePoly` quotients and a
remainder); Lean rebuilds the polynomials, confirms the remainder vanishes, and
reduces the goal to polynomial identities. The refinement this period was to keep
certificate *checking* cleanly separate from theorem *closing*: the checker
rebuilds and validates the certificate, and the final discharge is a separate,
configurable step. The default is the strongest one — a kernel re-check, so the CAS
is never trusted and trust rests only on the Lean kernel and the in-Lean checker —
but the separation is what makes the checker reusable across backends and the
finishing step swappable (see Row 4). On the development branches this generalizes
to **six certificate types, all kernel-checked with no added axioms**
(factorization, ideal membership/quotient–remainder, Gröbner-basis reduction,
radical membership, polynomial divisibility, permutation-group membership). The
"formally verified inside Lean, ensuring trust" outcome holds.
*Evidence:* `Macaulean/IdealMembership.lean`, `MacauleanTest/TestGB5Pts.lean`
(on `main`); the broader strategy set and `CAS_ARCHITECTURE.md` on the CAS branches
(`cas-design`, `groebner-tactic`).

### Row 4 — Q3 2026
**Output:** *Develop efficient proof tactics in Lean to handle computational algebra results.*
**Outcome:** *Provides reusable tools for verifying CAS computations in theorem proving.*

**On track on breadth; efficiency and extensibility are the current frontier (and
the project's main risk).** A reusable suite already exists: on `main`,
`m2idealmem`, `m2remainder`, `m2factor`/`m2reducible`; on branches, Gröbner-basis
reduction (`gb_reduce`), sum-of-squares (`m2sos`), a `polyrith`-style certificate
tactic (`m2polyrith`), a reflective algebra-normalizer (`algebra_norm`, on a
from-scratch two-level `AlgPoly` type), and radical-membership / divisibility /
permutation-group strategies.

The design refinement now being implemented is **modularity in the finishing
step**. Rather than forcing every problem through one expensive kernel-checked
hammer, the tactic reduces the goal to concrete polynomial identities and lets the
user choose how to discharge them: the built-in `grind`, a coefficient-by-coefficient
check, modular sampling (reduce mod several small primes and recover over ℚ/ℤ), or
simply handing the simpler goal back to the user to finish by hand. This leverages
human and external effort where it is cheaper than the kernel, and it widens
coverage to problems where no single automated discharger succeeds. The key
efficiency mitigation is already on `main` — the compact `ConcretePoly`
representation, which mirrors Macaulay2's term structure and is **parameterized over
its coefficient ring** (the mechanism for moving beyond ℚ, including the mod-p work
now underway). The 9-variable example verifies with a raised heartbeat budget;
pushing to substantially larger certificates is the open Q3 work (explored ideas:
sorted term-lists, monomial reordering, syzygy/GrevLex-shortened certificates,
modular techniques with CRT recovery, straight-line programs).
*Evidence:* `Macaulean/IdealMembership.lean` (`ConcretePoly`),
`MacauleanTest/TestGB5Pts.lean` (on `main`); `Macaulean/Grind/AlgPoly/*.lean`, the
`polyrith` branch.

### Row 5 — Q4 2026
**Output:** *Macaulay2 package dedicated to the Lean interface. Implementation of necessary data structures and methods.*
**Outcome:** *Provides a convenient interface for a Macaulay2 user to interact with Lean pursuing a goal of producing formal proofs of computational results.*

**Ahead of schedule, and stronger than a single package.** The Macaulay2 side
implements the interface and exposes semantic methods — a request/response main
loop, ideal membership returning quotient–remainder certificates as `ConcretePoly`
objects, factorization, sum-of-squares, and `toLean`/`fromLean` conversions
(`m2/macaulean.m2`), plus M2 classes mirroring Lean polynomial objects
(`m2/lean-mrdi.m2`) and MRDI validation (`m2/validate-mrdi.m2`). The most valuable
outcome here is that the reusable components have proven good enough to **seed the
broader Macaulay2 ecosystem rather than stay confined to one Lean-specific
package**: the JSON-RPC and MRDI layers are already upstreamed into the Macaulay2
distribution, so any Macaulay2 user gets the serialization/transport layer for free,
and because none of it is Lean-specific the same components can serve other proof
assistants. New work this period also includes an AI-assisted stored-artifact
prototype (M2 writes results to files that proofs reference) and a June prototype
that decomposes a CAS problem into atomic polynomial-identity tasks for Lean. The
remaining step to formally close this Q4 row is registering the project-specific
glue as an installable, named Macaulay2 package — though our emphasis is on keeping
the genuinely reusable pieces seeding the wider ecosystem.
*Evidence (on `main`):* `m2/macaulean.m2`, `m2/lean-mrdi.m2`,
`m2/validate-mrdi.m2`.

### Row 6 — Q4 2026
**Output:** *Implementation of Lean tactics to invoke Macaulay2 computations within proofs.*
**Outcome:** *Enables theorem proving workflows where AI-assisted proof generation can seamlessly incorporate CAS calculations.*

**Core capability achieved early.** Tactics that invoke Macaulay2 *within* a proof
and discharge the goal from the checked result work end-to-end on `main` (ideal
membership, factorization, remainder), demonstrated up to the 9-variable example.
The outcome's distinctive clause — *AI-assisted proof generation incorporating
CAS* — is shown most clearly by an episode in which an AI assistant drove
Macaulay2's sum-of-squares package over JSON-RPC to build the `m2sos` tactic live.
More broadly, AI coding assistants have been a routine part of how the
implementation gets written, which is part of why the build-out has moved quickly.
*Evidence (on `main`):* `Macaulean/IdealMembership.lean`,
`MacauleanTest/TestGB5Pts.lean`.

### Row 7 — Q1 2027
**Output:** *Investigate theorem prover interfaces within Macaulay2, in particular proof synthesis.*
**Outcome:** *Bridges the gap between symbolic computation and formal mathematics by allowing CAS-generated results to be directly formalized.*

**Started early (this is a Q1 2027 item).** We have begun investigating
Macaulay2-side proof synthesis: a June prototype in which Macaulay2 decomposes a
computation (ideal membership, exhibiting a Gröbner basis, computing a dimension)
into a list of **atomic, machine-checkable tasks** plus a meta-theorem asserting
their equivalence to the original statement, then ships those tasks to Lean to be
discharged. The general benefit we are aiming at is broader than feeding bite-size
pieces to the Lean kernel: a CAS that can emit a structured, verifiable account of
*why* its answer is correct produces certificates that any consumer — Lean today,
another assistant or an independent checker tomorrow — can audit, and that
decomposition is reusable independently of how the leaves are ultimately
discharged. A related direction Anton is keen to pursue is widening the *kinds* of
questions beyond polynomial identities — e.g. verifying factorizations into
irreducibles or primality via modular reduction and recovery — because those keep a
genuine Lean↔Macaulay2 interplay at the center rather than reducing to a pure
Lean proof problem. This is the "CAS-generated results directly formalized"
direction, begun ahead of its scheduled quarter, still exploratory.
*Evidence:* `m2/macaulean.m2` (June prototype); design discussion on the CAS
branches.

### Row 8 — Q2 2027
**Output:** *Publish framework for a general CAS-theorem prover integration model.*
**Outcome:** *Establishes a blueprint for connecting theorem provers with CAS beyond Macaulay2.*

**On track; the generalization is already demonstrated, and dissemination has
begun.** The architecture is a CAS-agnostic model (capability-advertising backends,
MRDI interchange, a strict separation between certificate-checking and the
configurable finishing step), and the generalization claim is **shown, not
asserted**: on the development branches, beyond Macaulay2 we added a **SymPy**
backend (Gröbner bases, factorization, radical membership) and an **Oscar/Julia**
backend (permutation-group membership via GAP), each plugging into the same core.
Dissemination: a contribution on the Lean–Macaulay2 interface was **accepted for
ICMS 2026 (Waterloo)** (with an invited talk by Michael Stillman); the design is
documented in `CAS_ARCHITECTURE.md` (CAS branches); and the MRDI/JSON-RPC layer is
now shipped with Macaulay2. Formal publication of the general framework remains the
Q2 2027 target.
*Evidence:* `Macaulean/SymPy.lean`, `Macaulean/Oscar.lean`,
`Macaulean/PermGroup.lean`, `sympy/macaulean_sympy.py`, `oscar/macaulean_oscar.jl`,
`CAS_ARCHITECTURE.md` (CAS branches).

---

## Status vs. the approved proposal: deviations and mitigations

We flag these proactively because a careful reader will compare against the
approved plan.

- **Mathlib alignment → core `grind` instead.** The proposal anticipated building
  on Mathlib's algebraic hierarchy. We found that wrapping Mathlib's `MvPolynomial`
  is hostile to kernel-level verification and instead built on Lean's core `grind`
  representation behind an implementation-agnostic interface — a smaller, faster,
  more auditable core. This dovetails with the bigger conceptual shift this period:
  away from "one powerful hammer that must always succeed in the kernel" and toward
  an extensible pipeline where the CAS round-trip is fixed but the finishing step is
  the user's choice (plug in a discharger, finish by a cheaper route, or accept
  Macaulay2's computation at a chosen trust level). A Mathlib-facing layer can still
  sit on top without disturbing the core.
- **Core on `main` vs. breadth on branches.** The three backends, the six-strategy
  set, the AlgPoly normalizer, and permutation-group membership are validated on
  active branches rather than `main`. To be clear about what is settled vs. still in
  flight: the *core* pipeline and the ideal-membership smoke test are settled on
  `main`; the breadth on branches is real and tested but is partly exploratory
  (which strategies are worth promoting, and how the finishing-step modularity
  should be exposed, are still being decided). Consolidation onto `main` is in
  progress. This is a sequencing choice, not abandoned work.
- **Coefficient generality (ℤ/p, char-p).** Strongest over ℚ/ℤ today; the
  `ConcretePoly` representation is parameterized over its coefficient ring, which is
  the structural mechanism now in place for ℤ/p and richer coefficients. Mod-p
  support is actively being added, which also opens modular/CRT finishing routes and
  applications like primality checking.
- **Macaulay2 package.** Strong here: the JSON-RPC and MRDI layers are upstreamed
  into Macaulay2. The open step for the Q4 2026 row is registering the remaining
  project-specific glue as an installable package — with the deliberate emphasis on
  keeping the reusable components seeding the wider ecosystem rather than locking
  them into one package.

## By the numbers (verified against the repo)

- **6** core contributors: Matthew Ballard, Anton Leykin, Michael Stillman
  (Macaulay2 co-creator), Damiano Testa, Jay Yang, Douglas Torrance.
- **3** CAS backends behind one interface (Macaulay2, SymPy, Oscar/GAP).
- **6** certificate-bearing strategies, **0** added axioms (kernel `decide`).
- End-to-end smoke test verified on `main`: a **10-generator ideal in 9 variables**
  (`MacauleanTest/TestGB5Pts.lean`).
- Part of the interface (**JSON-RPC + MRDI**) **now distributed with Macaulay2**.

## Engagement and dissemination

- **ICMS 2026 (Waterloo):** contribution **accepted**; **invited talk** by Michael
  Stillman.
- **Upcoming:** the **AI for Math** event in **London, Sep 17–18, 2026**; Georgia
  Tech / Macaulay2 visits.
- **External interest / collaboration:** a UK group formalizing the **LMFDB** has
  expressed interest in our polynomial-verification work; and the newly funded
  **Mathlib Initiative** (Alex Gerko/XTX; a Sloan Foundation gift to expand
  Mathlib's *computational* capabilities) is now active in this exact space — its
  first PR on verified computer algebra (computing determinants via the `ring`
  tactic) landed recently. We are in active talks with the Initiative about
  collaboration and shared hiring (below).

## Risks, resourcing, and where the next half goes

- **Kernel verification performance is the dominant risk** and the main current
  focus. Mitigations in progress: the compact `ConcretePoly` representation, the
  modular/CRT finishing routes, and the atomic-task decomposition. Upstream Lean
  improvements to recursion-depth and large-term handling would directly unlock
  larger instances; engagement with the Lean core team and the Mathlib Initiative on
  this is valuable.
- **Coefficient generality** beyond ℚ/ℤ is being addressed via the
  coefficient-parameterized representation, with mod-p support underway.
- **Consolidation and packaging** (merging the branch breadth onto `main`;
  registering an installable Macaulay2 package) are near-term engineering steps, not
  research risks.
- **Resourcing, looking forward.** With the core design settled, the next half is
  implementation-heavy, and we want to deploy effort where it compounds. There is
  room on the Lean side in particular, and rather than hiring narrowly for "someone
  to write Lean code for commutative algebra" — a thin labor market — the most
  leveraged move may be to **interlace with the Mathlib Initiative's verified-CAS
  work**, e.g. topping up one of their hires or scoping shared work at the seam
  between their efficient in-Lean computation and our CAS-certificate approach. We
  would welcome RenPhil's guidance on structuring such a collaboration.
