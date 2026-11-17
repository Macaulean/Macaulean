# Coding-agent task: prove an already approved M2 contract

Use this task only after the human has approved the contract and exported the
manifest. Replace the paths if the human selected other locations.

> Prove the frozen contract in `.macaulean/identity-job.json`.
>
> Read the exact target and relevant Lean definitions. Write one complete Lean
> proof **term** (`by ...` or a term expression), without a declaration header,
> to `.macaulean/candidates/attempt-001.proof`. Do not copy the checked-in test
> candidate. Reusing a generic, already checked lemma is legitimate; read its
> actual statement and justify that it applies to this frozen function/state.
>
> Run `python3 scripts/m2_proof_jobs.py .macaulean/identity-job.json
> .macaulean/candidates/attempt-001.proof --project "$PWD"
> --toolchain "$(lean --print-prefix)" --output .macaulean/proof-attempts`.
> Inspect the retained synthesis/validation diagnostics and revise the candidate
> in a new file until accepted or the human's attempt budget is exhausted.
>
> You may write candidate terms, local proof lemmas inside those terms, and
> explanatory notes under `.macaulean/candidates`. Do not modify executable M2,
> contracts, predicates, imported Lean definitions, approval directives, manifests,
> the runner/checker, or the baseline build. Do not run candidate tactics outside
> the supplied sandbox. Do not introduce axioms, `sorry`, admitted hypotheses,
> native-evaluation trust axioms, disabled kernel checks or hidden assumptions.
>
> If the exported job becomes stale, stop and report the change. Never refresh
> an approval token or strengthen a precondition to make the proof pass. A failed
> proof, missing artifact, skipped check, timeout or unavailable sandbox is not
> success. Do not claim an algebraic theorem when you only proved an execution
> equality, or termination when the target claims only partial correctness.
>
> On success, return the exact job fingerprint, the runner's evidence directory,
> and its `proof.json` path. State that the person must use `#m2_replay_proof`
> in the original worksheet before the editor accepts the proof. On failure,
> return the retained attempt paths and the precise remaining goal or diagnostic.

## Useful starting points

- `Macaulean/Verification/Contracts.lean`: fixed domain and postcondition.
- `Macaulean/Verification/Targets.lean`: the precise stateful target construction.
- `Macaulean/Interpreter/Runtime.lean`: actual closure and evaluation semantics.
- `Macaulean/Verification/ProofJobs/Identity.lean`: generic identity-call laws.
- `Macaulean/Verification/ViewLaws.lean`: polynomial/row decoding laws.

The runner does not start an agent for you. It is the validation tool that your
chosen coding agent invokes. A provider-specific continuous service is not part
of this smoke test. Existing test candidates are regression fixtures, not a
substitute for observing your chosen agent produce and repair its own candidate.
