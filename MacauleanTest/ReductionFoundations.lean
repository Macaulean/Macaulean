import Macaulean.Verification.ReductionDispatch
import Macaulean.Verification.ReductionTypes
import Macaulean.Verification.ReductionRow
import Macaulean.Verification.ReductionCoefficient
import Macaulean.Verification.ReductionRepresentation
import Macaulean.Verification.ReductionEffects
import Macaulean.Verification.CallNormal

namespace Macaulean.M2.Verification.ReductionFoundations.Tests
open Views ExecutionEffects ReductionEffects ReductionValues
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private def ring : Polynomials.RingInfo := ⟨13,["x"]⟩
private def poly (ts : List (Rat × Nat)) : Views.Polynomial ring :=
  ⟨⟨ts.map fun (c,n) => ⟨c,⟨[n],rfl⟩⟩⟩⟩
private def canceled := poly [(2,3),(-2,3),(0,0)]

example : evalBinOp .eq canceled.value (.zz 0) = .ok (.bool true) := by decide +kernel
example (powers : List Nat) : canceled.coeff powers = 0 :=
  eq_zero_coefficients canceled (by decide +kernel) powers

private def initial : Runtime.State := { heap := { cells := [.zz 99] } }
private def selectorArg : Value := .sequence [(poly [(1,1)]).value,
  .list [.list [(poly [(1,2)]).value,.list []], .list [(poly [(1,1)]).value,.list []]],.zz 0]

-- The selector must recurse past the first non-divisor and retain caller cells.
example : (Runtime.call 100 (.algebra (.library "m2gbReducer")) selectorArg initial).toOption.map
    (fun (v,s) => (v,s.heap.cells.take 1)) = some (.zz 1,[.zz 99]) := by decide +kernel

-- The exact move boundary: the fourth argument's addition exhausts depth 8,
-- while depth 9 reaches a recursive zero branch. Caller cells survive both.
private def moveLocals : List Value :=
  GCD.Execution.reductionLocals (poly [(1,1)]).value (.list []) (.list []) (poly []).value
private def moveState : Runtime.State := (initial.allocate moveLocals).2
private def moveFrames : Runtime.Frames := [GCD.Execution.frame initial 8]
example : Runtime.eval 8 GCD.Execution.reductionMoveHead moveFrames moveState =
    .error (.error .fuelExhausted) := by rfl
example : (Runtime.eval 9 GCD.Execution.reductionMoveHead moveFrames moveState).toOption.map
    (fun (v,s) => (v,s.heap.cells.take 1)) =
    some (.list [(poly [(1,1)]).value,.list []],[.zz 99]) := by decide +kernel

-- Dispatch also has a checked low-fuel boundary on a nonzero input.
example : Runtime.call 9 (.algebra (.library "m2gbReduce"))
    (.sequence [(poly [(1,1)]).value,.list [],.list [],(poly []).value]) initial =
    .error (.error .fuelExhausted) := by rfl

private def ring2 : Polynomials.RingInfo := ⟨17,["x","y"]⟩
private def monomial2 (a b : Nat) : Views.Polynomial ring2 :=
  ⟨⟨[⟨1,⟨[a,b],rfl⟩⟩]⟩⟩
example : Polynomials.callPrimitive .monomialQuotient
    (.sequence [(monomial2 2 1).value,(monomial2 1 1).value]) =
    .ok (monomial2 1 0).value := by decide +kernel
-- Failed divisibility and malformed dimensions cannot masquerade as typed results.
example : (Polynomials.callPrimitive .monomialQuotient
    (.sequence [(monomial2 1 1).value,(monomial2 2 1).value])).toOption = none := by decide +kernel
example : (Polynomials.monomialQuotient 2 [(1,[2,1])] [(1,[1])]).toOption = none := by decide +kernel
example : evalBinOp .mul (.qq 0) (monomial2 2 1).value =
    .ok (Views.Polynomial.mk (ring := ring2) ⟨[]⟩).value := by decide +kernel
example : evalBinOp .index (.list [(monomial2 2 1).value,(monomial2 1 1).value]) (.zz (-1)) =
    .ok (monomial2 1 1).value := by decide +kernel

-- The source coefficient expression executes without changing its frame.
private def coefficientLocals : List Value :=
  [(monomial2 2 1).value,.list [],.list [],(monomial2 0 0).value,
    .zz 0,.null,.list [(monomial2 1 1).value,.list []],.null]
private def coefficientState := (initial.allocate coefficientLocals).2
example : (Runtime.eval 10 GCD.Execution.reductionCoefficient
    [GCD.Execution.frame initial 8] coefficientState).toOption.map
    (fun (v,s) => (v,s.heap.cells)) =
    some ((monomial2 1 0).value,coefficientState.heap.cells) := by decide +kernel
example : (ReductionCoefficient.operations (monomial2 2 1)
    (Views.Polynomial.mk (ring := ring2) ⟨[]⟩)).toOption = none := by decide +kernel

-- The effect checker must not silently accept global mutation, arbitrary
-- dynamic calls, or the special remainder dispatch to normalForm.
example : ¬ ReadOnly [] (.set (.global "x") (.int 1)) := by intro h; cases h
example : ¬ ReadOnly [] (.apply (.read (.global "unknown")) (.int 1)) := by
  intro h
  cases h with
  | globalCall member _ => simp at member
example : ¬ ReadOnly [] (.binop .rem (.int 1) (.int 1)) := by
  intro h
  cases h with
  | binop notRem _ _ => exact notRem rfl

open Lean Elab Command in
run_cmd do
  let names := [``ExecutionEffects.evaluate, ``ExecutionEffects.library_safe,
    ``selector_readOnly, ``selector_safe, ``selector_preserves, ``row_readOnly, ``row_safe,
    ``ReductionValues.eval_eq_zero, ``eq_zero_coefficients, ``lead_term,
    ``ReductionValues.reduction_zero, ``representation_zero,
    ``Runtime.library_call_normal, ``Runtime.builtin_call_normal,
    ``Fuel.eval_mono, ``Runtime.Normal.catchReturn_eq,
    ``ReductionMove.execute, ``ReductionMove.successful,
    ``ReductionDispatch.expose, ``ReductionDispatch.successful,
    ``ReductionTypes.quotient_shape, ``ReductionTypes.lead_coefficient,
    ``ReductionTypes.lead_monomial, ``ReductionTypes.monomial_quotient,
    ``ReductionTypes.scalar_mul, ``ReductionTypes.index_member, ``ReductionTypes.selected_reducer,
    ``ReductionRow.invariant, ``ReductionRow.successful,
    ``ReductionCoefficient.operations_typed, ``ReductionCoefficient.execute,
    ``ReductionCoefficient.successful, ``ReductionCoefficient.normal,
    ``ReductionCancelTail.expose, ``ReductionCancelTail.successful,
    ``ReductionCancel.expose, ``ReductionCancel.successful, ``ReductionRepresentation.representation]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"REDUCTION_FOUNDATIONS_COMPLETE: {names.length} theorem dependency audits"

end Macaulean.M2.Verification.ReductionFoundations.Tests
