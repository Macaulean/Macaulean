import MacauleanMathlib.Buchberger
import MacauleanTest.CertificateCommands

open Macaulean.Verification.Mathlib

-- Actual worksheet membership certificates retain their mathematical meaning
-- when interpreted in Mathlib, over either supported coefficient family.
example : polynomial RationalCertificateTest.f_math.data ∈
    Ideal.span (polynomial '' {g | g ∈ RationalCertificateTest.I_math.generators.map (·.data)}) :=
  worksheet_generated_mem_span _ RationalCertificateTest.f_in_I

example : polynomial FiniteCertificateTest.f_math.data ∈
    Ideal.span (polynomial '' {g | g ∈ FiniteCertificateTest.I_math.generators.map (·.data)}) :=
  worksheet_generated_mem_span _ FiniteCertificateTest.f_in_I

-- The existing equality certificate also identifies the standard ideals.
example : Ideal.span (polynomial '' {g | g ∈
      FiniteCertificateTest.same_ideal.ideal.generators.map (·.data)}) =
    Ideal.span (polynomial '' {g | g ∈
      FiniteCertificateTest.same_ideal.basis.output.generators.map (·.data)}) :=
  worksheet_checked_sameIdeal _ FiniteCertificateTest.same_ideal.checked

-- Degree takes precedence over the reverse lexicographic tie-breaker.
example : (grevlexOrder 3).toSyn (exponents ⟨[0,0,2],rfl⟩) <
    (grevlexOrder 3).toSyn (exponents ⟨[3,0,0],rfl⟩) := by
  apply (grevlexOrder_lt_iff _ _).mpr
  decide +kernel

-- At equal degree x*z < y^2: this distinguishes grevlex from lex.
example : (grevlexOrder 3).toSyn (exponents ⟨[1,0,1],rfl⟩) <
    (grevlexOrder 3).toSyn (exponents ⟨[0,2,0],rfl⟩) := by
  apply (grevlexOrder_lt_iff _ _).mpr
  decide +kernel

-- Every finite-dimensional grevlex order is well founded, not only these examples.
example (n : Nat) : WellFoundedLT (grevlexOrder n).syn := inferInstance

-- The empty basis certifies the zero ideal without a hidden nonempty assumption.
private def emptyCertificate : BuchbergerCertificate (R := Rat) (grevlexOrder 2)
    (fun i : Fin 0 => nomatch i) where
  monic i := nomatch i
  pairs i := nomatch i
example : (grevlexOrder 2).IsGroebnerBasis
    (Set.range (fun i : Fin 0 => (nomatch i : MvPolynomial (Fin 2) Rat)))
    (Ideal.span (Set.range (fun i : Fin 0 => (nomatch i : MvPolynomial (Fin 2) Rat)))) :=
  emptyCertificate.isGroebnerBasis

-- A nonempty monic basis certifies the unit ideal, with zero S-pairs.
private noncomputable def unitCertificate : BuchbergerCertificate (R := Rat) (grevlexOrder 2)
    (fun _ : Fin 1 => 1) where
  monic _ := by simp
  pairs _ _ := {
    coefficients := fun _ => 0
    identity := by simp [MonomialOrder.sPolynomial_self]
    degreeBound := by intro i; simp [MonomialOrder.sPolynomial_self]
  }
example : (grevlexOrder 2).IsGroebnerBasis
    (Set.range (fun _ : Fin 1 => (1 : MvPolynomial (Fin 2) Rat)))
    (Ideal.span (Set.range (fun _ : Fin 1 => (1 : MvPolynomial (Fin 2) Rat)))) :=
  unitCertificate.isGroebnerBasis

/-- info: 'Macaulean.Verification.Mathlib.BuchbergerCertificate.isGroebnerBasis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BuchbergerCertificate.isGroebnerBasis

/-- info: 'Macaulean.Verification.Mathlib.grevlexOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grevlexOrder

/-- info: 'Macaulean.Verification.Mathlib.polynomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms polynomial_mul
