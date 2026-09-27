# Stage 2: fixed proof jobs and generic proofs

Stacked on Stage 1 PR #38 at `0e48783ad691e53310315153dcd8ab665ac246ba`.

This is an implementation checkpoint, not a completion or validation claim.

## Work plan

1. Export exact, source-approved contract targets as immutable proof jobs.
2. Check candidate proofs independently of the worker; record exact target,
   dependency, source and axiom evidence. Approval and proof remain separate.
3. Add a bounded external-worker protocol with isolated attempts and retained
   diagnostics; ordinary elaboration must never wait for a model request.
4. Establish generic coefficient-row/reduction invariant lemmas, and connect
   a completed generic source-level proof to the same acceptance path used by
   external workers. Concrete execution examples are not universal proofs.
5. Exercise replay, refusal, cancellation, stale targets, and InfoView evidence.

Workers may propose proof terms and proved helper lemmas. They may not edit the
fixed target, the approved contract or executable source; approve intent; declare
new trusted assumptions; or turn missing output into success. Clean replay is the
acceptance criterion, not a worker's reported verdict.

No real contract is approved by development fixtures. A source attestation is
not authentication of its author. Provider credentials and unattended background
services are not installed or started by importing a Lean module.

The final PR description will distinguish completed generic theorems, conditional
bridge lemmas, executable tests, external-worker integration, and any remaining
semantic or deployment boundaries.
