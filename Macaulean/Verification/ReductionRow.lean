import Macaulean.Verification.RowRepresentation
import Macaulean.Verification.ReductionValues

/-! Cancellation's representation invariant through the executed row helper. -/
namespace Macaulean.M2.Verification.ReductionRow
open Views PolynomialArithmetic PolynomialRows ProofJobs.RuntimeReduction

/-- Pointwise row subtraction preserves the full pending-plus-remainder
representation, for arbitrary dimensions and noncanonical polynomials. -/
theorem invariant (generators coefficients updated : Row r n)
    (pending remainder c product nextPending : Views.Polynomial r)
    (g : RepresentedReducer r n)
    (input : InputInvariant generators pending remainder coefficients)
    (reducer : ReducerInvariant generators g)
    (rows : Subtracts c coefficients.values g.coefficients.values updated.values)
    (multiply : evalBinOp .mul c.value g.polynomial.value = .ok product.value)
    (subtract : evalBinOp .sub pending.value product.value = .ok nextPending.value) :
    InputInvariant generators nextPending remainder updated := by
  let balance : Views.Polynomial r := ⟨KernelPolynomial.add pending.data remainder.data⟩
  have represented : ∀ powers, balance.coeff powers =
      linearCoefficient coefficients.values generators.values powers := by
    intro powers
    exact (coeff_add pending remainder powers).trans (input powers)
  have result := rows.represents generators.values balance g.polynomial represented reducer
  intro powers
  have balanceEq := cancel_balance_coefficients pending remainder c g.polynomial product
    nextPending multiply subtract powers
  rw [← result powers, coeff_sub, coeff_mul]
  simpa only [balance, coeff_add] using balanceEq

/-- The row helper's execution facts do not require a representation invariant. -/
theorem successful_step (coefficients : Row r n) (c : Views.Polynomial r)
    (other : Row r n) (s after : Runtime.State) (fuel : Nat) (v : Value)
    (global : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")))
    (success : Runtime.call fuel (.algebra (.library "m2gbSubtractRow"))
      (.sequence [coefficients.value,c.value,other.value,.zz 0]) s = .ok (v,after)) :
    ∃ updated : Row r n, v = updated.value ∧
      Subtracts c coefficients.values other.values updated.values ∧
      RowProgram.AllocatesOnly s after := by
  obtain ⟨updated,expected,run,rows,effects⟩ := execute c coefficients other s 0 global
  have same := Fuel.call_success_unique fuel (0+16*(n+1)) _ _ s _ _ success run
  refine ⟨updated,congrArg Prod.fst same,rows,?_⟩
  have stateEq : after = expected := congrArg Prod.snd same
  rw [stateEq]
  exact effects

/-- A successful actual row-helper call at any budget supplies the updated
representation invariant and retains all pre-existing cells and bindings.
The known total execution is compared at the original budget; the caller's
recursive budget is never increased. -/
theorem successful (generators coefficients : Row r n)
    (pending remainder c product nextPending : Views.Polynomial r)
    (g : RepresentedReducer r n)
    (input : InputInvariant generators pending remainder coefficients)
    (reducer : ReducerInvariant generators g)
    (multiply : evalBinOp .mul c.value g.polynomial.value = .ok product.value)
    (subtract : evalBinOp .sub pending.value product.value = .ok nextPending.value)
    (s after : Runtime.State) (fuel : Nat) (v : Value)
    (global : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")))
    (success : Runtime.call fuel (.algebra (.library "m2gbSubtractRow"))
      (.sequence [coefficients.value,c.value,g.coefficients.value,.zz 0]) s = .ok (v,after)) :
    ∃ updated : Row r n, v = updated.value ∧
      InputInvariant generators nextPending remainder updated ∧
      RowProgram.AllocatesOnly s after := by
  obtain ⟨updated,valueEq,rows,effects⟩ :=
    successful_step coefficients c g.coefficients s after fuel v global success
  exact ⟨updated,valueEq,invariant generators coefficients updated pending remainder c product
    nextPending g input reducer rows multiply subtract,effects⟩

end Macaulean.M2.Verification.ReductionRow
