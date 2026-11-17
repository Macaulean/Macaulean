import Macaulean.Verification.Proofs

/-!
Ordinary M2 and deterministic intent review come first. This example approves
nothing and starts no service. Review the contract in the Stage 1 InfoView panel;
only a current source-attested proposal may be exported as a proof job.

See docs/m2-proof-smoke.md for the Linux worker setup and exact agent prompt.
-/
open M2
samePolynomial = p -> p;
#m2_contract "samePolynomial" polynomialIdentity

-- Use the panel's consent checkbox and Record approval in source button.
-- Never ask a proof agent to create or refresh that approval directive.
-- After approval, uncomment this export command BELOW the approval:
-- #m2_export_proof_job "samePolynomial" polynomialIdentity ".macaulean/identity-job.json"

-- An external coding agent writes a Lean term, then runs scripts/m2_proof_jobs.py.
-- That runner constructs a proof in one sandbox and independently checks the
-- serialized term in a fresh sandbox. Its receipt alone is not editor evidence.
-- Replace the placeholder below with the runner's reported proof.json path:
-- #m2_replay_proof "samePolynomial" polynomialIdentity "<evidence directory>/proof.json"
-- #m2_proof_status "samePolynomial" polynomialIdentity

-- Status is relative to its source snapshot. Earlier intent panels do not
-- retroactively become proofs. Changed code or revoked approval must be rejected.
-- This pilot exposes proof evidence through #m2_proof_status; it does not launch
-- a continuous model service or implement the later combined evidence panel.
