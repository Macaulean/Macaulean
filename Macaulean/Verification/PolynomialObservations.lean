import Macaulean.Verification.CoefficientLaws

/-! Linear observations and extensionality for sparse polynomials. Coefficient
equality determines arbitrary weighted sums, without canonical-form assumptions. -/
namespace Macaulean.M2.KernelPolynomial
open Lean.Grind

theorem mon_mul_assoc (a b c : Mon n) : (a.mul b).mul c = a.mul (b.mul c) := by
  apply Mon.powers_eq_iff_eq.mp
  simp only [Mon.mul]
  have go (xs ys zs : List Nat) :
      List.zipWith (· + ·) (List.zipWith (· + ·) xs ys) zs =
      List.zipWith (· + ·) xs (List.zipWith (· + ·) ys zs) := by
    induction xs generalizing ys zs with
    | nil => simp
    | cons x xs ih =>
      cases ys <;> cases zs <;> simp [ih, Nat.add_assoc]
  exact go _ _ _

theorem weightedSum_weight_add (f g : Mon n → Rat) (ts : List (PolyTerm Rat n)) :
    weightedSum (fun m => f m + g m) ts = weightedSum f ts + weightedSum g ts := by
  induction ts with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih => simp only [weightedSum, ih]; grind

theorem weightedSum_weight_scale (a : Rat) (f : Mon n → Rat) (ts : List (PolyTerm Rat n)) :
    weightedSum (fun m => a * f m) ts = a * weightedSum f ts := by
  induction ts with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih => simp only [weightedSum, ih]; grind

theorem weightedSum_mul_assoc (w : Mon n → Rat) (a b c : Polynomial Rat n) :
    weightedSum w (mul (mul a b) c).terms = weightedSum w (mul a (mul b c)).terms := by
  simp only [weightedSum_mul, mon_mul_assoc]

theorem weightedSum_weight_congr (f g : Mon n → Rat) (ts : List (PolyTerm Rat n))
    (h : ∀ m, f m = g m) : weightedSum f ts = weightedSum g ts := by
  have : f = g := funext h
  rw [this]

theorem weightedSum_split (w : Mon n → Rat) (m : Mon n) (ts : List (PolyTerm Rat n)) :
    weightedSum w ts = w m * weightedSum (fun k => if k = m then 1 else 0) ts +
      weightedSum (fun k => if k = m then 0 else w k) ts := by
  rw [← weightedSum_weight_scale, ← weightedSum_weight_add]
  apply weightedSum_weight_congr
  intro k
  split <;> simp_all <;> grind

theorem weightedSum_vanish (ts : List (PolyTerm Rat n)) (w : Mon n → Rat)
    (h : ∀ m, w m ≠ 0 → weightedSum (fun k => if k = m then 1 else 0) ts = 0) :
    weightedSum w ts = 0 := by
  induction ts generalizing w with
  | nil => rfl
  | cons t ts ih =>
    let w' := fun k => if k = t.monomial then 0 else w k
    have hz : weightedSum w' ts = 0 := by
      apply ih
      intro m hm
      have ne : m ≠ t.monomial := by
        intro eq
        simp [w', eq] at hm
      have hw : w m ≠ 0 := by simpa [w', ne] using hm
      have hh := h m hw
      simp [weightedSum, Ne.symm ne] at hh
      grind
    rw [weightedSum_split w t.monomial (t::ts)]
    have rest : weightedSum (fun k => if k = t.monomial then 0 else w k) (t::ts) = 0 := by
      simp only [weightedSum]
      change t.coefficient * 0 + weightedSum w' ts = 0
      rw [hz]
      grind
    rw [rest]
    by_cases hw : w t.monomial = 0
    · rw [hw]; grind
    · rw [h t.monomial hw]; grind

theorem weightedSum_ext (p q : Polynomial Rat n)
    (h : ∀ m, weightedSum (fun k => if k = m then 1 else 0) p.terms =
      weightedSum (fun k => if k = m then 1 else 0) q.terms) (w : Mon n → Rat) :
    weightedSum w p.terms = weightedSum w q.terms := by
  have hz := weightedSum_vanish (sub p q).terms w (by
    intro m _
    rw [weightedSum_sub, h m]
    grind)
  rw [weightedSum_sub] at hz
  grind

theorem indicator_coefficient (ts : List (PolyTerm Rat n)) (m : Mon n) :
    weightedSum (fun k => if k = m then 1 else 0) ts =
      Verification.Views.coefficient (ts.map fun t => (t.coefficient,t.monomial.powers)) m.powers := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [weightedSum, List.map_cons, Verification.Views.coefficient_cons, ih,
      Mon.powers_eq_iff_eq]
    split <;> simp_all <;> grind

theorem weightedSum_weight_zero (ts : List (PolyTerm Rat n)) :
    weightedSum (fun _ => 0) ts = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [weightedSum, ih]; grind

theorem weightedSum_mul_add_right (w : Mon n → Rat) (a b c : Polynomial Rat n) :
    weightedSum w (mul a (add b c)).terms =
      weightedSum w (mul a b).terms + weightedSum w (mul a c).terms := by
  simp only [weightedSum_mul, weightedSum_add, weightedSum_weight_add]

end Macaulean.M2.KernelPolynomial
namespace Macaulean.M2.Verification.Views
open KernelPolynomial

theorem equivalent_weighted (p q : Polynomial r) (h : Equivalent p q)
    (w : Macaulean.Mon r.names.length → Rat) :
    weightedSum w p.data.terms = weightedSum w q.data.terms := by
  apply weightedSum_ext
  intro m
  rw [indicator_coefficient, indicator_coefficient]
  exact h m.powers
end Macaulean.M2.Verification.Views
