import Macaulean.Interpreter.GCD.Automatic
import Macaulean.Interpreter.GCD.ComputeCorrectness

namespace Macaulean.M2.GCD.Execution
open Macaulean.M2.Runtime Univariate

theorem automatic_call_eq (depth : Nat) (arg : Value) (s : State) :
    call (depth+1) (.algebra (.library "gcd")) arg s handler =
      callWithBudget arg s := by
  simp [call, handler, bind, Except.bind, pure, Except.pure]

/-- The worksheet call handler runs the same proved source in the caller's state.
The surrounding depth only needs to reach the function call. -/
theorem automatic_call_correct (depth : Nat) (f g : Value) (s : State)
    (globals : GCDGlobals s)
    (hd : s.env.lookup "m2GCDInputs" = some (.algebra (.builtin .gcdInputs)))
    (valid : ∃ data, Polynomials.gcdInputs (.sequence [f,g]) = .ok data) :
    ∃ (id : Nat) (name : String) (p q out : Poly) (after : State),
      Canonical p.terms ∧ Canonical q.terms ∧ Canonical out.terms ∧ MonicOrZero out ∧
      Polynomials.gcdInputs (.sequence [f,g]) =
        .ok (ringInfo id name,Polynomials.encode p,Polynomials.encode q) ∧
      TotalCorrectness.IsGCD Divides p q out ∧ Extends s after ∧
      call (depth+1) (.algebra (.library "gcd")) (.sequence [f,g]) s handler =
        .ok (value id name out,after) := by
  obtain ⟨data,hvalid⟩ := valid
  obtain ⟨id,name,p,q,hp,hq,hin⟩ := validated_has_canonical f g data hvalid
  have hdata : Polynomials.callPrimitive .gcdInputs
      (.sequence [value id name p,value id name q]) =
      .ok (.list [value id name p,value id name q]) := by
    simp only [Polynomials.callPrimitive, gcd_inputs_canonical id name p q hp hq,
      bind, Except.bind, pure, Except.pure]
    rfl
  obtain ⟨out,after,ho,hm,hgcd,he,run⟩ := gcd_entry_correct id name
    (.sequence [value id name p,value id name q]) p q hp hq hdata s globals hd
    _ (input_fuel_sufficient p q)
  refine ⟨id,name,p,q,out,after,hp,hq,ho,hm,hin,hgcd,he,?_⟩
  rw [automatic_call_eq]
  simp only [callWithBudget, hin, liftResult, Except.mapError, bind, Except.bind]
  exact run

end Macaulean.M2.GCD.Execution
