import Macaulean.Interpreter.GCD.ComputeCorrectness

namespace Macaulean.M2.GCD
open Univariate

/-- A concrete worksheet result is a monic GCD of the validated input
polynomials, with the same runtime ring identity. -/
def ValueSpec (f g result : Value) : Prop :=
  ∃ (id : Nat) (name : String) (p q out : Poly),
    Canonical p.terms ∧ Canonical q.terms ∧ Canonical out.terms ∧ MonicOrZero out ∧
    Polynomials.gcdInputs (.sequence [f,g]) =
      .ok (ringInfo id name,Polynomials.encode p,Polynomials.encode q) ∧
    result = value id name out ∧ TotalCorrectness.IsGCD Divides p q out

/-- Specialize the universal correctness theorem to a concrete computed value.
The execution equality must itself be checked by Lean. -/
theorem certify_result (f g result : Value) (run : compute f g = .ok result) :
    ValueSpec f g result := by
  have valid : ∃ data, Polynomials.gcdInputs (.sequence [f,g]) = .ok data := by
    cases hin : Polynomials.gcdInputs (.sequence [f,g]) with
    | error e => simp [compute, hin, bind, Except.bind] at run
    | ok data => exact ⟨data,rfl⟩
  obtain ⟨id,name,p,q,out,hp,hq,hin,ho,hm,hgcd,hex⟩ := Execution.compute_total f g valid
  have heq : result = value id name out := Except.ok.inj (run.symm.trans hex)
  exact ⟨id,name,p,q,out,hp,hq,ho,hm,hin,heq,hgcd⟩

end Macaulean.M2.GCD
