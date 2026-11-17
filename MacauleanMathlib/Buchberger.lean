import MacauleanMathlib.GroebnerTheory.Groebner
import MacauleanMathlib.Grevlex
import MacauleanMathlib.Worksheet
import Macaulean.Algebra.Certificates

/-!
# Soundness interface for finite Gröbner certificates

A representation of an S-polynomial must satisfy the degree bound, not just
membership in the generated ideal. This interface packages exactly the evidence
needed by the proved Buchberger criterion, for an indexed finite basis (including
an empty basis and repeated generators).
-/
namespace Macaulean.Verification.Mathlib
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MvPolynomial
variable {R : Type} [CommRing R] {n k : Nat}

/-- A zero-remainder certificate with one coefficient for every basis element. -/
structure BoundedRepresentation (m : MonomialOrder (Fin n))
    (basis : Fin k → MvPolynomial (Fin n) R) (f : MvPolynomial (Fin n) R) where
  coefficients : Fin k → MvPolynomial (Fin n) R
  identity : f = ∑ i, coefficients i * basis i
  degreeBound : ∀ i,
    m.toWithBotSyn (m.withBotDegree (basis i)) +
      m.toWithBotSyn (m.withBotDegree (coefficients i)) ≤ m.toWithBotSyn (m.withBotDegree f)

theorem BoundedRepresentation.isRemainder {m : MonomialOrder (Fin n)}
    {basis : Fin k → MvPolynomial (Fin n) R} {f : MvPolynomial (Fin n) R}
    (c : BoundedRepresentation m basis f) : m.IsRemainder f (Set.range basis) 0 := by
  classical
  rw [MonomialOrder.IsRemainder.isRemainder_range]
  refine ⟨⟨Finsupp.equivFunOnFinite.symm c.coefficients, ?_, ?_⟩, ?_⟩
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), add_zero]
    simpa only [Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul] using c.identity
  · exact c.degreeBound
  · simp

/-- All leading coefficients are one, and every S-pair has a bounded representation.
The checker will establish these fields from executable certificate data. -/
structure BuchbergerCertificate (m : MonomialOrder (Fin n))
    (basis : Fin k → MvPolynomial (Fin n) R) where
  monic : ∀ i, m.leadingCoeff (basis i) = 1
  pairs : ∀ i j, BoundedRepresentation m basis (m.sPolynomial (basis i) (basis j))

theorem BuchbergerCertificate.isGroebnerBasis {m : MonomialOrder (Fin n)}
    {basis : Fin k → MvPolynomial (Fin n) R} (c : BuchbergerCertificate m basis) :
    m.IsGroebnerBasis (Set.range basis) (Ideal.span (Set.range basis)) := by
  apply (MonomialOrder.IsGroebnerBasis.iff_isRemainder_sPolynomial_zero ?_).mpr
  · rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    exact (c.pairs i j).isRemainder
  · rintro _ ⟨i, rfl⟩
    rw [c.monic]
    exact isUnit_one

variable [DecidableEq R]

/-- An accepted two-way certificate identifies the standard Mathlib ideals too. -/
theorem checked_sameIdeal {input basis : List (Macaulean.Polynomial R n)}
    {forward backward : List (List (Macaulean.Polynomial R n))}
    (h : Macaulean.Algebra.Certificates.sameIdeal input basis forward backward = true) :
    Ideal.span (polynomial '' {g | g ∈ input}) =
      Ideal.span (polynomial '' {g | g ∈ basis}) := by
  have hs := Macaulean.Algebra.Certificates.sameIdeal_sound h
  apply le_antisymm <;> apply Ideal.span_le.mpr
  · rintro _ ⟨p, hp, rfl⟩
    exact generated_mem_span ((hs p).mp (.generator hp))
  · rintro _ ⟨p, hp, rfl⟩
    exact generated_mem_span ((hs p).mpr (.generator hp))


/-- Two-way worksheet certificates identify the Mathlib ideals, preserving the
core field instance used when their polynomial identities were checked. -/
theorem worksheet_checked_sameIdeal (F : Macaulean.Algebra.CoefficientField)
    {input basis : List (Macaulean.Polynomial F.Carrier n)}
    {forward backward : List (List (Macaulean.Polynomial F.Carrier n))}
    (h : Macaulean.Algebra.Certificates.sameIdeal input basis forward backward = true) :
    Ideal.span (polynomial '' {g | g ∈ input}) =
      Ideal.span (polynomial '' {g | g ∈ basis}) := by
  have hs := Macaulean.Algebra.Certificates.sameIdeal_sound h
  apply le_antisymm <;> apply Ideal.span_le.mpr
  · rintro _ ⟨p, hp, rfl⟩
    exact worksheet_generated_mem_span F ((hs p).mp (.generator hp))
  · rintro _ ⟨p, hp, rfl⟩
    exact worksheet_generated_mem_span F ((hs p).mpr (.generator hp))

end
end Macaulean.Verification.Mathlib
