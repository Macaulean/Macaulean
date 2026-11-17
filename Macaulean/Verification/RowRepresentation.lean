import Macaulean.Verification.PolynomialRows
import Macaulean.Verification.PolynomialObservations

/-! Preservation of linear combinations by the executed polynomial-row helper.
The conclusion uses the existing coefficientwise `Views.Represents` relation,
not an assumed arithmetic law or a separate evaluator. -/
namespace Macaulean.M2.Verification.PolynomialRows
open Views KernelPolynomial
open Lean.Grind

def linearPolynomial : List (Views.Polynomial r) → List (Views.Polynomial r) →
    Views.Polynomial r
  | [], _ => ⟨⟨[]⟩⟩
  | _, [] => ⟨⟨[]⟩⟩
  | a::as, b::bs => ⟨add (mul a.data b.data) (linearPolynomial as bs).data⟩

theorem linearPolynomial_coeff (xs gs : List (Views.Polynomial r)) (powers : List Nat) :
    (linearPolynomial xs gs).coeff powers = linearCoefficient xs gs powers := by
  induction xs generalizing gs with
  | nil => rfl
  | cons x xs ih =>
    cases gs with
    | nil => rfl
    | cons g gs =>
      change (Views.Polynomial.mk (add (mul x.data g.data) (linearPolynomial xs gs).data)).coeff powers = _
      rw [coeff_add, coeff_mul, ih]
      rfl

theorem Subtracts.weighted {c : Views.Polynomial r}
    {xs ys zs : List (Views.Polynomial r)} (h : Subtracts c xs ys zs)
    (gs : List (Views.Polynomial r)) (w : Macaulean.Mon r.names.length → Rat) :
    weightedSum w (linearPolynomial zs gs).data.terms =
      weightedSum w (linearPolynomial xs gs).data.terms -
      weightedSum w (mul c.data (linearPolynomial ys gs).data).terms := by
  induction h generalizing gs with
  | nil =>
    simp only [linearPolynomial, weightedSum_mul, weightedSum, weightedSum_weight_zero]
    grind
  | @cons x y z xs ys zs coeff tail ih =>
    cases gs with
    | nil =>
      simp only [linearPolynomial, weightedSum_mul, weightedSum, weightedSum_weight_zero]
      grind
    | cons g gs =>
      have eq : Equivalent z ⟨sub x.data (mul c.data y.data)⟩ := by
        intro powers
        rw [coeff_sub, coeff_mul, coeff]
      have hz := equivalent_weighted z ⟨sub x.data (mul c.data y.data)⟩ eq
        (fun m => weightedSum (fun k => w (m.mul k)) g.data.terms)
      simp only [weightedSum_sub] at hz
      rw [← weightedSum_mul, ← weightedSum_mul, ← weightedSum_mul] at hz
      rw [weightedSum_mul_assoc] at hz
      simp only [linearPolynomial, weightedSum_add, weightedSum_mul_add_right]
      rw [hz, ih]
      grind

theorem Subtracts.represents {c : Views.Polynomial r}
    {xs ys zs : List (Views.Polynomial r)} (h : Subtracts c xs ys zs)
    (gs : List (Views.Polynomial r)) (p q : Views.Polynomial r)
    (hp : ∀ powers, p.coeff powers = linearCoefficient xs gs powers)
    (hq : ∀ powers, q.coeff powers = linearCoefficient ys gs powers) :
    ∀ powers, (Views.Polynomial.mk (sub p.data (mul c.data q.data))).coeff powers =
      linearCoefficient zs gs powers := by
  have ep : Equivalent p (linearPolynomial xs gs) := by
    intro powers
    rw [linearPolynomial_coeff, hp]
  have eq : Equivalent q (linearPolynomial ys gs) := by
    intro powers
    rw [linearPolynomial_coeff, hq]
  intro powers
  rw [← linearPolynomial_coeff, coeff_weighted, coeff_weighted, h.weighted]
  rw [weightedSum_sub, weightedSum_mul, weightedSum_mul]
  rw [equivalent_weighted p _ ep]
  simp only [equivalent_weighted q _ eq]

theorem execute_represents (c p q : Views.Polynomial r) (gs : List (Views.Polynomial r))
    (xs ys : Row r gs.length) (hp : Represents p gs xs) (hq : Represents q gs ys)
    (s : Runtime.State) (spare : Nat)
    (global : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow"))) :
    ∃ (zs : Row r gs.length) (after : Runtime.State),
      Runtime.call (spare + 16*(gs.length+1)) (.algebra (.library "m2gbSubtractRow"))
        (.sequence [xs.value,c.value,ys.value,.zz 0]) s = .ok (zs.value,after) ∧
      Represents ⟨sub p.data (mul c.data q.data)⟩ gs zs ∧
      RowProgram.AllocatesOnly s after := by
  obtain ⟨zs,after,run,spec,effects⟩ := execute c xs ys s spare global
  exact ⟨zs,after,run,spec.represents gs p q hp hq,effects⟩

end Macaulean.M2.Verification.PolynomialRows
