import Macaulean.Verification.Proofs

/-! Synthetic end-to-end worker fixture. This test's explicit attestation is not
approval of a real project contract. Never copy the synthetic approval mechanism
into an agent process or update a real token automatically after an edit. -/
namespace Stage2SyntheticFixture
open Lean Elab Command
open Macaulean.M2 Macaulean.M2.Verification
open _root_.M2

toyIdentity = p -> p;
#m2_contract "toyIdentity" polynomialIdentity

run_cmd do
  let entry ← Index.ensure "toyIdentity" (← DSL.getSession)
  let index ← Index.get
  let some proposal := index.ledger.find entry.id .polynomialIdentity
    | throwError "synthetic proposal missing"
  let ledger ← match index.ledger.approve entry.id .polynomialIdentity
      proposal.payload proposal.digest "SYNTHETIC WORKER TEST ONLY" with
    | .ok l => pure l | .error e => throwError e
  Index.put { index with ledger }

#m2_export_proof_job "toyIdentity" polynomialIdentity "ci-evidence/stage2-target.json"
end Stage2SyntheticFixture
