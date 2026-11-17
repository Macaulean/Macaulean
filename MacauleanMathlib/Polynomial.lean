import Mathlib
import Macaulean.Algebra.Polynomial

/-!
# Standard multivariate-polynomial interpretation

Sparse polynomial presentations denote elements of Mathlib's `MvPolynomial`.
The interpretation preserves coefficients, including over finite fields, rather
than identifying polynomials that happen to have the same values.
-/
namespace Macaulean.Verification.Mathlib

noncomputable section

variable {n : Nat}

/-- Variables retain their positions in the exported ordered variable list. -/
def exponents (m : Macaulean.Mon n) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m.powers[i.val]'(by simpa only [m.powers_length] using i.isLt))

@[simp] theorem exponents_apply (m : Macaulean.Mon n) (i : Fin n) :
    exponents m i = m.powers[i.val]'(by simpa only [m.powers_length] using i.isLt) := rfl

def monomial (e : Fin n →₀ ℕ) : Macaulean.Mon n :=
  ⟨List.ofFn e, by simp⟩

@[simp] theorem exponents_monomial (e : Fin n →₀ ℕ) : exponents (monomial e) = e := by
  ext i
  simp [monomial]

@[simp] theorem monomial_exponents (m : Macaulean.Mon n) : monomial (exponents m) = m := by
  apply Macaulean.Mon.powers_eq_iff_eq.mp
  apply List.ext_getElem
  · simp [monomial, m.powers_length]
  · intro i hi hj
    simp [monomial, exponents]

 theorem exponents_injective : Function.Injective (exponents (n := n)) := by
  intro a b h
  simpa using congrArg monomial h

variable {R : Type} [CommRing R] [DecidableEq R]

/-- Sum the monomials; duplicates and zero terms are semantically harmless. -/
def polynomial (p : Macaulean.Polynomial R n) : MvPolynomial (Fin n) R :=
  (p.terms.map fun t => MvPolynomial.monomial (exponents t.monomial) t.coefficient).sum

omit [DecidableEq R] in
theorem coefficient_polynomial (p : Macaulean.Polynomial R n) (m : Macaulean.Mon n) :
    MvPolynomial.coeff (exponents m) (polynomial p) =
      Macaulean.Algebra.Polynomial.coefficient p m := by
  rcases p with ⟨ts⟩
  induction ts with
  | nil => simp [polynomial, Macaulean.Algebra.Polynomial.coefficient,
      Macaulean.M2.KernelPolynomial.weightedSum]
  | cons t ts ih =>
    simp [polynomial, Macaulean.Algebra.Polynomial.coefficient,
      Macaulean.M2.KernelPolynomial.weightedSum] at ih ⊢
    rw [ih]
    by_cases h : t.monomial = m
    · simp [h]
    · have he : exponents t.monomial ≠ exponents m := fun he => h (exponents_injective he)
      simp [h, he]

omit [DecidableEq R] in
theorem polynomial_eq_iff (p q : Macaulean.Polynomial R n) :
    polynomial p = polynomial q ↔ Macaulean.Algebra.Polynomial.Equivalent p q := by
  constructor
  · intro h m
    rw [← coefficient_polynomial, ← coefficient_polynomial, h]
  · intro h
    ext e
    have hh := h (monomial e)
    simpa only [← coefficient_polynomial, exponents_monomial] using hh

 theorem polynomial_normalize (p : Macaulean.Polynomial R n) :
    polynomial (Macaulean.M2.KernelPolynomial.normalize p) = polynomial p :=
  (polynomial_eq_iff _ _).mpr (Macaulean.Algebra.Polynomial.normalize_equivalent p)

@[simp] theorem exponents_mul (a b : Macaulean.Mon n) :
    exponents (a.mul b) = exponents a + exponents b := by
  ext i
  simp [exponents, Macaulean.Mon.mul]

omit [DecidableEq R] in
@[simp] theorem polynomial_zero :
    polynomial (Macaulean.Algebra.Polynomial.zero : Macaulean.Polynomial R n) = 0 := rfl

theorem polynomial_add (p q : Macaulean.Polynomial R n) :
    polynomial (Macaulean.M2.KernelPolynomial.add p q) = polynomial p + polynomial q := by
  rw [Macaulean.M2.KernelPolynomial.add, polynomial_normalize]
  simp [polynomial]

omit [DecidableEq R] in
theorem polynomial_neg (p : Macaulean.Polynomial R n) :
    polynomial p.neg = -polynomial p := by
  simp [polynomial, Macaulean.Polynomial.neg, List.sum_neg, Function.comp_def]

theorem polynomial_sub (p q : Macaulean.Polynomial R n) :
    polynomial (Macaulean.M2.KernelPolynomial.sub p q) = polynomial p - polynomial q := by
  simp [Macaulean.M2.KernelPolynomial.sub, polynomial_add, polynomial_neg, sub_eq_add_neg]

omit [DecidableEq R] in
theorem polynomial_mulMonTerms (c : R) (m : Macaulean.Mon n)
    (ts : List (Macaulean.PolyTerm R n)) :
    polynomial ⟨Macaulean.Polynomial.mulMonTerms c m ts⟩ =
      MvPolynomial.monomial (exponents m) c * polynomial ⟨ts⟩ := by
  induction ts with
  | nil => simp [polynomial, Macaulean.Polynomial.mulMonTerms]
  | cons t ts ih =>
    simpa [polynomial, Macaulean.Polynomial.mulMonTerms, mul_add, MvPolynomial.monomial_mul]
      using congrArg (fun x => MvPolynomial.monomial (exponents (m.mul t.monomial))
        (c * t.coefficient) + x) ih

theorem polynomial_mul (p q : Macaulean.Polynomial R n) :
    polynomial (Macaulean.M2.KernelPolynomial.mul p q) = polynomial p * polynomial q := by
  rw [Macaulean.M2.KernelPolynomial.mul, polynomial_normalize]
  rcases p with ⟨ts⟩
  induction ts with
  | nil => simp [polynomial]
  | cons t ts ih =>
    change polynomial ⟨Macaulean.Polynomial.mulMonTerms t.coefficient t.monomial q.terms ++
      ts.flatMap (fun t => Macaulean.Polynomial.mulMonTerms t.coefficient t.monomial q.terms)⟩ = _
    have append (a b : List (Macaulean.PolyTerm R n)) :
        polynomial ⟨a ++ b⟩ = polynomial ⟨a⟩ + polynomial ⟨b⟩ := by simp [polynomial]
    rw [append, polynomial_mulMonTerms, ih]
    simp [polynomial, add_mul]

/-- Generated-ideal membership transports to the standard mathematical ideal. -/
theorem generated_mem_span {gs : List (Macaulean.Polynomial R n)}
    {p : Macaulean.Polynomial R n} (hp : Macaulean.Algebra.Generated gs p) :
    polynomial p ∈ Ideal.span (polynomial '' {g | g ∈ gs}) := by
  induction hp with
  | zero => simp only [polynomial_zero]; exact Ideal.zero_mem _
  | generator h => exact Ideal.subset_span ⟨_, h, rfl⟩
  | add _ _ ihp ihq => rw [polynomial_add]; exact Ideal.add_mem _ ihp ihq
  | mul a _ ih => rw [polynomial_mul]; exact Ideal.mul_mem_left _ _ ih
  | equivalent h _ ih => rwa [← (polynomial_eq_iff _ _).mpr h]

end
end Macaulean.Verification.Mathlib
