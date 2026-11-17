# Run the proof pipeline with a coding agent

Branch: `feature/m2-proof-stage2-20260927` (PR #39, stacked on #38).
The supported pilot entry point is `Macaulean.Verification.Proofs` and the
`scripts/m2_proof_jobs.py` runner. The earlier `ProofCommands` prototype is
retained on the branch, but it is not the interface described here.

## Platform and initial gate

The isolated worker requires **Linux, Python 3, bubblewrap and the repository's
pinned Lean toolchain**. Unprivileged user namespaces must be available. There is
no unsandboxed fallback. On macOS use a Linux VM or a remote Linux development
host; this is not a native macOS worker. No model credential is required to run
the gate, and none is passed to the Lean worker processes.

In a clean checkout:

```sh
git fetch origin
git switch --track origin/feature/m2-proof-stage2-20260927
# On Debian/Ubuntu, if not already installed:
sudo apt-get update && sudo apt-get install -y bubblewrap python3
bash scripts/m2_proof_smoke.sh
```

With an existing local branch, switch to it and fast-forward normally instead of
creating another tracking branch. The script expects `lean` and `lake` on PATH
(e.g. through elan); `lean-toolchain` selects the pinned release.

The gate builds the real Lean modules, runs the protocol tests, exports a
**synthetic** approved identity target, checks two candidate terms in separate
synthesis/validation sandboxes, rejects a hole and invalid candidates, and
replays the accepted packet in fresh Lean processes. It also requires rejection
after code changes and revocation. It retains logs and exit codes under
`ci-evidence/`. Missing tools, sandbox failure or timeout are failures, not skips.

One candidate is a regression proof; the other was authored by the assistant as
an ordinary proof candidate. The gate does not call a hosted model API, and is
not evidence that an unattended model service has been deployed.

## 1. A person approves the intended contract

Open `Examples/ProofReview.lean` in Lean:

```lean
import Macaulean.Verification.Proofs
open M2

samePolynomial = p -> p;
#m2_contract "samePolynomial" polynomialIdentity
```

Review the InfoView card, including the fact that this is **partial correctness
on successful returns**, not a termination or effect-preservation claim. Use its
consent checkbox and **Record approval in source**. The editor inserts a literal
`#m2_approve` with the current fingerprint. Do not let the proof agent insert or
refresh this approval, and do not copy the synthetic test's approval mechanism.

Below the approval, add:

```lean
#m2_export_proof_job "samePolynomial" polynomialIdentity
  ".macaulean/identity-job.json"
```

Elaborate the worksheet. The export is refused unless the approval is current.
The manifest contains the exact closed Lean proposition and its semantic seal.
Do not add new M2 runtime inputs between approval and export/replay: Stage 1
conservatively pins the full initial runtime state.

## 2. Have an agent generate a candidate and use real diagnostics

Give your coding agent `docs/m2-proof-agent-task.md` and the exported manifest.
It should write a Lean **term** such as `by ...` into
`.macaulean/candidates/attempt-001.proof`, not a new module or theorem header.
It may inspect the trusted source and reuse its generic lemmas. It may not edit
the implementation, approved target, schema, approval, checker or baseline build.

The agent runs:

```sh
python3 scripts/m2_proof_jobs.py \
  .macaulean/identity-job.json \
  .macaulean/candidates/attempt-001.proof \
  --project "$PWD" \
  --toolchain "$(lean --print-prefix)" \
  --output .macaulean/proof-attempts
```

The exit status matters. Failed attempts retain the candidate, target and
process stdout/stderr for repair. The agent can submit a revised term by invoking
the same command with another candidate file. A successful response identifies
an immutable evidence directory containing `target.json`, `proof.json`,
`receipt.json`, and `context.sha256`.

The runner snapshots the baseline, mounts it read-only, and starts two different
processes. Candidate tactics execute only in the synthesis sandbox. The validator
receives the serialized expression, not candidate tactic source, and forces
synchronous kernel checking and an axiom audit. New helper declarations are not
silently imported; put local lemmas inside the proof term or separately review
and build reusable helpers before exporting a new job.

## 3. Replay in the original worksheet

Copy the runner's reported `proof.json` path into:

```lean
#m2_replay_proof "samePolynomial" polynomialIdentity
  "<reported evidence directory>/proof.json"
#m2_proof_status "samePolynomial" polynomialIdentity
```

Re-elaborate the file. Replay independently checks the proof against the current
source-approved target. It does not trust the receipt's status string. The
resulting status message identifies the checked theorem. Closing and reopening
Lean must reproduce that result from the source and packet.

Proof status is currently an explicit command message. Stage 1's earlier intent
card does not retroactively become a proof-evidence card. Continuous monitoring,
a combined evidence panel and provider integration remain separate work.

## 4. Check the failure behavior

Change `p -> p` to `p -> p+1` without changing the literal approval. The old
approval/proof must be refused. Restore the body and make only a comment or
parenthesis edit; the old proof should replay. Revoke the approval with
`#m2_revoke "samePolynomial" polynomialIdentity`; proof replay must then fail.

Do **not** ask an agent to fix either negative test by refreshing the approval,
weakening the target, suppressing diagnostics or using `sorry`.

## What the pilot does not establish

The identity result is generic over admissible inputs, not a one-input execution
certificate. The branch also contains generic coefficient-row/conservation laws.
The actual `m2gbReduce` representation and irreducibility targets are explicitly
still unproved. A passing smoke test establishes the proof-job mechanism, not
universal correctness of the Gröbner-basis algorithm or completion of all Stage 2.
