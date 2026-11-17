import Macaulean.Verification.ProofJobs.Frontend

/-! Opt-in Stage 2 proof-job export and kernel replay. No model call runs during
ordinary elaboration. Source intent approval and proof evidence remain separate.
The existing Stage 1 panel remains an intent panel; `#m2_proof_status` displays
replayed evidence explicitly until the combined evidence panel is integrated. -/
