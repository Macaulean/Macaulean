# Stage 2: proof-pipeline pilot

PR #39 is stacked on Stage 1 #38 at
`0e48783ad691e53310315153dcd8ab665ac246ba`, on branch
`feature/m2-proof-stage2-20260927`.

## Supported entry point

Use `import Macaulean.Verification.Proofs`, the
[single-command smoke test and human walkthrough](m2-proof-smoke.md), and
[the coding-agent task](m2-proof-agent-task.md). See the
[Linux sandbox prerequisites](m2-worker-linux.md) before running on Ubuntu.

```sh
bash scripts/m2_proof_smoke.sh
```

The implemented path is `Macaulean/Verification/ProofJobs/` plus
`scripts/m2_proof_jobs.py`. The older `ProofCommands`, `ProofCore`, `ProofData`,
`ProofServer`, `Evidence`, `GenericProofs` and `RowProgram` files are preserved
prototype work. Do not combine their commands/receipts with the supported
`ProofJobs` protocol or treat their presence as a completed agent service.

## What the pilot supplies

A person selects and approves a Stage 1 contract. The editor exports its exact
closed proposition and frozen implementation/state/dependency identity. A coding
agent writes a candidate proof term and invokes the runner. Synthesis executes
inside a restricted Linux namespace; an independent process receives only the
serialized expression and the frozen target. The accepting path forces
synchronous Lean kernel checking and audits the proof's dependency axioms.

The runner retains attempts and publishes complete evidence atomically. A success
receipt is diagnostic data, not authority. `#m2_replay_proof` recomputes the current
source-approved target and rechecks the packet. `#m2_proof_status` reports the
actual installed theorem for that revision. Stale/revoked approvals are rejected.

The semantic libraries are part of the immutable baseline and are loaded in both
processes to accelerate elaboration and fingerprinting. They do not replace
kernel checking with native evaluation. Candidate-created declarations are not
transferred into the accepting environment. Both filesystem and network namespace
isolation remain required; no unsandboxed or network-sharing fallback exists.

## Proofs and tests

`ProofJobs.Identity` proves the generic polynomial-identity contract for the real
lexical evaluator, for every admissible argument and successful evaluation in the
specified state. It also proves sufficient evaluation depth for that body.
`ProofJobs.Conservation` proves generic coefficient-row and transition-invariant
laws. These are not certificates for one numerical example.

The native gate exercises two real candidate terms, independent checking,
precise rejection of holes/invalid candidates, and fresh-process source replay.
One candidate is assistant-authored; the gate is not a hosted-model API test.
Protocol tests are explicitly separate from the real kernel and sandbox gate.
Logs, exact revisions and exit codes are retained as CI artifacts. The PR body
records which exact head has completed each gate; an in-progress run is not a
passing result.

## Remaining Stage 2 work

The actual `m2gbReduce` representation and irreducibility statements are explicit
unproved proposition definitions in `ProofJobs.RuntimeReduction`. Abstract
conservation does not discharge their interpreter/algebra correspondence. This
pilot does not claim those theorems, general termination, automatic verified
lifting or full Gröbner algorithm correctness.

There is no continuous background model coordinator or provider integration.
Your chosen coding agent invokes the runner explicitly. The combined InfoView
proof-evidence panel is also pending: Stage 1 cards remain intent cards, while
replayed evidence has its own status command.

No real project contract is approved by the fixtures. Source attestation is not
authentication of its author. Workers must not edit implementations, predicates,
approvals, trusted baselines or targets; they may only propose proofs. Existing
Lean axioms are audited under the declared allowlist, never silently expanded.
