import Macaulean.Verification.ReductionDispatch
import Macaulean.Verification.ReductionCancel

/-! Representation correctness of the actual multivariate reduction helper. -/
namespace Macaulean.M2.Verification.ReductionRepresentation
open Views ProofJobs.RuntimeReduction

/-- Every successful execution of the tracked four-argument source helper
returns a dimension-correct row representing its remainder in the original
generators. The theorem assumes neither canonical inputs nor termination. -/
theorem representation : RepresentationStatement := by
  intro r n generators pending remainder coefficients reducers input represented
    s fuel result after globals run
  induction fuel using Nat.strongRecOn generalizing pending remainder coefficients s result after with
  | ind fuel ih =>
    cases test : decide (Polynomials.encode (KernelPolynomial.normalize pending.data) = []) with
    | true =>
      have zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool true) := by
        rw [ReductionValues.eval_eq_zero, test]
      exact ReductionValues.representation_zero generators pending remainder coefficients reducers
        input zero s fuel result after run
    | false =>
      have nonzero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool false) := by
        rw [ReductionValues.eval_eq_zero, test]
      obtain ⟨j,branchState,negative,branchDepth,branchSmaller,_,frame,_,branchRun⟩ :=
        ReductionDispatch.successful fuel pending coefficients.value
          (.list (reducers.map RepresentedReducer.value)) remainder.value s after result globals nonzero run
      cases negative with
      | true =>
        obtain ⟨np,nr,next,depth,smaller,bindings,invariant,recursiveRun⟩ :=
          ReductionMove.successful branchDepth s branchState generators pending remainder coefficients
            (.list (reducers.map RepresentedReducer.value)) j .null .null .null result after
            frame globals input branchRun
        exact ih depth (by omega) (pending := np) (remainder := nr) (coefficients := coefficients)
          invariant next result after bindings recursiveRun
      | false =>
        obtain ⟨np,updated,next,depth,smaller,bindings,invariant,recursiveRun⟩ :=
          ReductionCancel.successful branchDepth s branchState after result generators coefficients
            pending remainder reducers j .null .null .null frame globals input represented branchRun
        exact ih depth (by omega) (pending := np) (remainder := remainder) (coefficients := updated)
          invariant next result after bindings recursiveRun

end Macaulean.M2.Verification.ReductionRepresentation
