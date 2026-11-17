import Macaulean.Verification.ReductionValues

/-! Coefficientwise irreducibility laws used by the source reduction proof. -/
namespace Macaulean.M2.Verification.IrreducibleArithmetic
open Views PolynomialArithmetic

/-- Adding two irreducible polynomials cannot introduce a reducible monomial,
even if either input has duplicate terms or cancellation occurs in the sum. -/
theorem add (p q out : Views.Polynomial r) (gs : List (Views.Polynomial r))
    (hp : Irreducible p gs) (hq : Irreducible q gs)
    (sum : evalBinOp .add p.value q.value = .ok out.value) : Irreducible out gs := by
  intro powers nonzero g member leading head
  by_cases left : p.coeff powers = 0
  · have right : q.coeff powers ≠ 0 := by
      intro zero
      apply nonzero
      rw [successful_add_coefficients p q out sum, left, zero, Rat.zero_add]
    exact hq powers right g member leading head
  · exact hp powers left g member leading head

/-- If no reducer divides the pending head, the actual leading-term primitive
produces an irreducible polynomial. No canonicality assumption is needed. -/
theorem leading_term (p : Views.Polynomial r) (gs : List (Views.Polynomial r))
    (noneDivides : ∀ powers, p.leadingPowers? = some powers →
      ∀ g ∈ gs, ∀ leading, g.leadingPowers? = some leading →
        Polynomials.divides leading powers = false) :
    Irreducible (Views.Polynomial.mk ⟨(KernelPolynomial.normalize p.data).terms.take 1⟩) gs := by
  intro powers nonzero g member leading head
  cases terms : (KernelPolynomial.normalize p.data).terms with
  | nil =>
    simp [Views.Polynomial.coeff, Views.Polynomial.raw, Polynomials.encode,
      coefficient, terms] at nonzero
  | cons t ts =>
    have same : t.monomial.powers = powers := by
      by_cases equal : t.monomial.powers = powers
      · exact equal
      · simp [Views.Polynomial.coeff, Views.Polynomial.raw, Polynomials.encode,
          coefficient, terms, equal, Rat.zero_add] at nonzero
    apply noneDivides powers _ g member leading head
    simp [Views.Polynomial.leadingPowers?, terms, same]

end Macaulean.M2.Verification.IrreducibleArithmetic
