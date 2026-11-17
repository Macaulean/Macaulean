import MacauleanMathlib.Polynomial
import Macaulean.Polynomial.Lemmas

/-! The worksheet's grevlex order as a well-founded mathematical monomial order. -/
namespace Macaulean.Verification.Mathlib
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A separate synonym keeps the coordinatewise order on `Finsupp` intact. -/
def GrevlexExponent (n : Nat) := Fin n →₀ ℕ

namespace GrevlexExponent
variable {n : Nat}

instance : AddCommMonoid (GrevlexExponent n) := inferInstanceAs (AddCommMonoid (Fin n →₀ ℕ))

def key (a : GrevlexExponent n) : ℕ ×ₗ (List ℕ)ᵒᵈ :=
  toLex ((monomial a).degree, OrderDual.toDual (monomial a).powers.reverse)

theorem key_injective : Function.Injective (key (n := n)) := by
  intro a b h
  have hp := congrArg (fun k => (ofLex k).2) h
  have hm : monomial a = monomial b :=
    Macaulean.Mon.powers_eq_iff_eq.mp (List.reverse_inj.mp hp)
  have h := congrArg exponents hm
  rw [exponents_monomial, exponents_monomial] at h
  exact h

instance : LinearOrder (GrevlexExponent n) := LinearOrder.lift' key key_injective

theorem lt_iff (a b : GrevlexExponent n) : a < b ↔ (monomial b).Grevlex (monomial a) := by
  change key a < key b ↔ _
  simp only [key, Prod.Lex.toLex_lt_toLex, Macaulean.Mon.Grevlex]
  change _ ↔ (monomial a).degree < (monomial b).degree ∨ _
  rw [eq_comm (a := (monomial b).degree)]
  rfl

@[simp] theorem monomial_add (a b : GrevlexExponent n) :
    monomial (a + b) = (monomial a).mul (monomial b) := by
  apply exponents_injective
  rw [exponents_mul, exponents_monomial, exponents_monomial, exponents_monomial]

instance : IsOrderedAddMonoid (GrevlexExponent n) where
  add_le_add_left a b hab c := by
    rcases hab.eq_or_lt with he | hlt
    · simp [he]
    · apply le_of_lt
      rw [add_comm a c, add_comm b c]
      rw [lt_iff, monomial_add, monomial_add]
      exact Macaulean.Mon.grevlex_mul_mono_left.mp ((lt_iff a b).mp hlt)

/-- Coordinatewise growth either preserves the monomial or increases total degree. -/
theorem coordinate_mono : Monotone (α := Fin n →₀ ℕ) (β := GrevlexExponent n) (fun a => a) := by
  intro a b hab
  by_cases he : a = b
  · subst b; exact le_rfl
  apply le_of_lt
  rw [lt_iff]
  apply Or.inl
  change (List.ofFn a).sum < (List.ofFn b).sum
  rw [List.sum_ofFn, List.sum_ofFn]
  apply Finset.sum_lt_sum (fun i _ => hab i)
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra! h
    exact he (Finsupp.ext h)
  exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hab i) hi⟩

instance : WellFoundedLT (GrevlexExponent n) := by
  have : WellQuasiOrderedLE (GrevlexExponent n) :=
    coordinate_mono.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective (fun a => ⟨a, rfl⟩)
  infer_instance

end GrevlexExponent

/-- Exactly the degree/reversed-exponent grevlex order used by the interpreter. -/
def grevlexOrder (n : Nat) : MonomialOrder (Fin n) where
  syn := GrevlexExponent n
  toSyn := AddEquiv.refl _
  toSyn_monotone := GrevlexExponent.coordinate_mono

/-- The formal order compares precisely the same exponent lists as the runtime. -/
theorem grevlexOrder_lt_iff (a b : Macaulean.Mon n) :
    (grevlexOrder n).toSyn (exponents a) < (grevlexOrder n).toSyn (exponents b) ↔
      a.grevlex b = .lt := by
  have h := GrevlexExponent.lt_iff (n := n) (exponents a) (exponents b)
  rw [monomial_exponents, monomial_exponents, Macaulean.Mon.grevlex_iff_grevlex_gt,
    ← Macaulean.Mon.grevlex_flip] at h
  exact h


end
end Macaulean.Verification.Mathlib
