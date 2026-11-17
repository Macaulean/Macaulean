import MacauleanMathlib.Polynomial
import MacauleanMathlib.CoefficientField

/-! Preserve the original worksheet's core ring instance when transporting proofs.
Its scalar/power structure fields differ from Mathlib's derived instance, even
though the coefficient operations used by these polynomials agree. -/
namespace Macaulean.Verification.Mathlib
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (F : Macaulean.Algebra.CoefficientField) {n : Nat}

 theorem worksheet_coefficient (p : Macaulean.Polynomial F.Carrier n) (m : Macaulean.Mon n) :
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

theorem worksheet_equivalent {p q : Macaulean.Polynomial F.Carrier n}
    (h : Macaulean.Algebra.Polynomial.Equivalent p q) : polynomial p = polynomial q := by
  ext e
  have hh := h (monomial e)
  simpa only [← worksheet_coefficient, exponents_monomial] using hh

theorem worksheet_normalize (p : Macaulean.Polynomial F.Carrier n) :
    polynomial (Macaulean.M2.KernelPolynomial.normalize p) = polynomial p :=
  worksheet_equivalent F (Macaulean.Algebra.Polynomial.normalize_equivalent p)

theorem worksheet_add (p q : Macaulean.Polynomial F.Carrier n) :
    polynomial (Macaulean.M2.KernelPolynomial.add p q) = polynomial p + polynomial q := by
  rw [Macaulean.M2.KernelPolynomial.add, worksheet_normalize]
  simp [polynomial]

theorem worksheet_mul (p q : Macaulean.Polynomial F.Carrier n) :
    polynomial (Macaulean.M2.KernelPolynomial.mul p q) = polynomial p * polynomial q := by
  rw [Macaulean.M2.KernelPolynomial.mul, worksheet_normalize]
  have h := polynomial_mul p q
  simp only [Macaulean.M2.KernelPolynomial.mul] at h
  rw [polynomial_normalize] at h
  exact h

theorem worksheet_sub (p q : Macaulean.Polynomial F.Carrier n) :
    polynomial (Macaulean.M2.KernelPolynomial.sub p q) = polynomial p - polynomial q := by
  rw [Macaulean.M2.KernelPolynomial.sub, worksheet_add, polynomial_neg, sub_eq_add_neg]

theorem worksheet_generated_mem_span
    {gs : List (Macaulean.Polynomial F.Carrier n)} {p : Macaulean.Polynomial F.Carrier n}
    (hp : Macaulean.Algebra.Generated gs p) :
    polynomial p ∈ Ideal.span (polynomial '' {g | g ∈ gs}) := by
  induction hp with
  | zero => simp only [polynomial_zero]; exact Ideal.zero_mem _
  | generator h => exact Ideal.subset_span ⟨_, h, rfl⟩
  | add _ _ ihp ihq => rw [worksheet_add]; exact Ideal.add_mem _ ihp ihq
  | mul a _ ih => rw [worksheet_mul]; exact Ideal.mul_mem_left _ _ ih
  | equivalent h _ ih => rwa [← worksheet_equivalent F h]

end
end Macaulean.Verification.Mathlib
