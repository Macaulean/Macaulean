import Macaulean.Verification.PolynomialArithmetic
import Macaulean.Interpreter.GCD.Reduction
import Macaulean.Verification.ProofJobs.RuntimeReduction
namespace Macaulean.M2.Verification.ReductionValues
open Views

theorem eval_eq_zero (p : Views.Polynomial r) :
    evalBinOp .eq p.value (.zz 0) =
      .ok (.bool (decide (Polynomials.encode (KernelPolynomial.normalize p.data) = []))) := by
  simp [evalBinOp, Polynomials.evalBinary, Polynomials.equal, Polynomials.matrixView?,
    Polynomials.common, Polynomials.polyRing?, Polynomials.cast, Polynomials.scalar?,
    Polynomials.constant, Polynomials.normalize_bridge, Polynomials.liftError,
    Except.mapError, Views.Polynomial.value, Views.Polynomial.raw,
    bind, Except.bind, pure, Except.pure]

theorem eq_zero_coefficients (p : Views.Polynomial r)
    (h : evalBinOp .eq p.value (.zz 0) = .ok (.bool true)) :
    ∀ powers, p.coeff powers = 0 := by
  rw [eval_eq_zero] at h
  have zero : Polynomials.encode (KernelPolynomial.normalize p.data) = [] := by
    simpa using h
  intro powers
  rw [← coeff_normalize p]
  change coefficient (Polynomials.encode (KernelPolynomial.normalize p.data)) powers = 0
  rw [zero]
  rfl
theorem lead_term (p : Views.Polynomial r) :
    Polynomials.callPrimitive .leadTerm p.value =
      .ok (Views.Polynomial.mk ⟨(KernelPolynomial.normalize p.data).terms.take 1⟩).value := by
  have encoded : Polynomials.encode (⟨(KernelPolynomial.normalize p.data).terms.take 1⟩ :
      Macaulean.Polynomial Rat r.names.length) =
      (Polynomials.encode (KernelPolynomial.normalize p.data)).take 1 := by
    simp [Polynomials.encode, List.map_take]
  simp [Polynomials.callPrimitive, Polynomials.unaryArg, Polynomials.unpack,
    Polynomials.asPolynomial, Polynomials.normalize_bridge, Polynomials.liftError,
    Except.mapError, Views.Polynomial.value, Views.Polynomial.raw, encoded,
    bind, Except.bind, pure, Except.pure]

open Lexical Macaulean.M2.Runtime GCD.Execution

theorem reduction_zero (fuel : Nat) (p : Views.Polynomial r) (row gs remainder : Value)
    (s : State) (zero : evalBinOp .eq p.value (.zz 0) = .ok (.bool true)) :
    call (fuel+10) (.algebra (.library "m2gbReduce"))
      (.sequence [p.value,row,gs,remainder]) s =
        .ok (.list [remainder,row],
          (s.allocate (reductionLocals p.value row gs remainder)).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s reduction_source (by rfl)]
  change catchReturn (eval (fuel+9) reductionBody
    [(s.allocate (reductionLocals p.value row gs remainder)).1]
    (s.allocate (reductionLocals p.value row gs remainder)).2) = _
  have h0 := allocated_read s (reductionLocals p.value row gs remainder) 0 p.value rfl
  have h1 := allocated_read s (reductionLocals p.value row gs remainder) 1 row rfl
  have h3 := allocated_read s (reductionLocals p.value row gs remainder) 3 remainder rfl
  simp only [reductionBody, localVar, eval, evalMany, h0, h1, h3, zero,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

open ProofJobs.RuntimeReduction in
theorem representation_zero (generators : Row r n) (pending remainder : Views.Polynomial r)
    (coefficients : Row r n) (reducers : List (RepresentedReducer r n))
    (input : InputInvariant generators pending remainder coefficients)
    (zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool true))
    (s : State) (fuel : Nat) (result : Value) (after : State)
    (success : call fuel (.algebra (.library "m2gbReduce"))
      (.sequence [pending.value,coefficients.value,
        .list (reducers.map RepresentedReducer.value),remainder.value]) s = .ok (result,after)) :
    ∃ (rv av : Value) (p : Views.Polynomial r) (a : Row r n),
      result = .list [rv,av] ∧ readPolynomial r rv = .ok p ∧ readRow r n av = .ok a ∧
      (∀ powers, p.coeff powers = linearCoefficient a.values generators.values powers) := by
  have base := reduction_zero 0 pending coefficients.value
    (.list (reducers.map RepresentedReducer.value)) remainder.value s zero
  have same := Fuel.call_success_unique fuel 10 _ _ s _ _ success base
  have resultEq := congrArg Prod.fst same
  refine ⟨remainder.value,coefficients.value,remainder,coefficients,resultEq,
    polynomial_roundtrip remainder,row_roundtrip coefficients,?_⟩
  intro powers
  have balance := input powers
  rw [eq_zero_coefficients pending zero powers] at balance
  simpa only [Rat.zero_add] using balance

end Macaulean.M2.Verification.ReductionValues
