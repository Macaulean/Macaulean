import Macaulean.Verification.ReductionDispatch
import Macaulean.Verification.ReductionCancel
import Macaulean.Verification.ReducerSelectionLaws

/-! Irreducibility of every successful source multivariate reduction result. -/
namespace Macaulean.M2.Verification.ReductionIrreducibility
open Views ProofJobs.RuntimeReduction

/-- The exact generic runtime target. Initial remainder irreducibility is
preserved by cancellation, and a moved head is justified by the actual ordered
selector's negative result. No representation or termination hypothesis is used. -/
theorem irreducible : IrreducibleStatement := by
  intro r n pending remainder coefficients reducers irreducible s fuel result after globals run
  induction fuel using Nat.strongRecOn generalizing pending remainder coefficients s result after with
  | ind fuel ih =>
    cases test : decide (Polynomials.encode (KernelPolynomial.normalize pending.data) = []) with
    | true =>
      have zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool true) := by
        rw [ReductionValues.eval_eq_zero, test]
      have stop := ReductionValues.reduction_zero 0 pending coefficients.value
        (.list (reducers.map RepresentedReducer.value)) remainder.value s zero
      have same := Fuel.call_success_unique fuel 10 _ _ s _ _ run stop
      exact ⟨remainder.value,coefficients.value,remainder,congrArg Prod.fst same,
        polynomial_roundtrip remainder,irreducible⟩
    | false =>
      have nonzero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool false) := by
        rw [ReductionValues.eval_eq_zero, test]
      obtain ⟨j,branchState,negative,branchDepth,selected,selectorDepth,
          branchSmaller,_,frame,cmp,selectorRun,branchRun⟩ :=
        ReductionDispatch.successful_selected fuel pending coefficients.value
          (.list (reducers.map RepresentedReducer.value)) remainder.value s after result globals nonzero run
      cases negative with
      | true =>
        have headIrreducible := ReducerSelection.negative_leading_term pending reducers
          (s.allocate (GCD.Execution.reductionLocals pending.value coefficients.value
            (.list (reducers.map RepresentedReducer.value)) remainder.value)).2
          selected selectorDepth j (globals.allocate _) selectorRun cmp
        obtain ⟨np,nr,next,depth,smaller,bindings,_,sum,recursiveRun⟩ :=
          ReductionMove.successful_step branchDepth s branchState pending remainder coefficients
            (.list (reducers.map RepresentedReducer.value)) j .null .null .null result after
            frame globals branchRun
        have nextIrreducible := IrreducibleArithmetic.add remainder _ nr _ irreducible headIrreducible sum
        exact ih depth (by omega) (pending := np) (remainder := nr) (coefficients := coefficients)
          nextIrreducible next result after bindings recursiveRun
      | false =>
        obtain ⟨c,product,np,g,updated,next,depth,smaller,bindings,_,_,_,_,recursiveRun⟩ :=
          ReductionCancel.successful_step branchDepth s branchState after result coefficients
            pending remainder reducers j .null .null .null frame globals branchRun
        exact ih depth (by omega) (pending := np) (remainder := remainder) (coefficients := updated)
          irreducible next result after bindings recursiveRun

end Macaulean.M2.Verification.ReductionIrreducibility
