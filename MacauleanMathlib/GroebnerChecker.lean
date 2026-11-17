import Macaulean.Algebra.GroebnerCertificates
import MacauleanMathlib.Buchberger

/-! Soundness of the executable leading-term, degree-bound, and S-pair checks. -/
namespace Macaulean.Verification.Mathlib
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Macaulean.Algebra.GroebnerCertificates
open MvPolynomial
variable {R : Type} [CommRing R] [DecidableEq R] {n : Nat}

omit [DecidableEq R] in
private theorem coefficient_zero_of_absent (ts : List (Macaulean.PolyTerm R n))
    (e : Fin n →₀ ℕ) (h : ∀ t ∈ ts, exponents t.monomial ≠ e) :
    coeff e (polynomial ⟨ts⟩) = 0 := by
  induction ts with
  | nil => simp [polynomial]
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs := ih (fun u hu => h u (by simp [hu]))
    simpa [polynomial, ht] using hs

omit [DecidableEq R] in
private theorem support_term {p : Macaulean.Polynomial R n} {e : Fin n →₀ ℕ}
    (h : e ∈ (polynomial p).support) : ∃ t ∈ p.terms, exponents t.monomial = e := by
  by_contra! hn
  exact (mem_support_iff.mp h) (coefficient_zero_of_absent p.terms e hn)

/-- A checked head is the mathematical leading term, including its coefficient. -/
theorem checked_head {t : Macaulean.PolyTerm R n} {ts : List (Macaulean.PolyTerm R n)}
    (h : leadingTerms (t :: ts) = true) :
    (grevlexOrder n).degree (polynomial ⟨t :: ts⟩) = exponents t.monomial ∧
    (grevlexOrder n).leadingCoeff (polynomial ⟨t :: ts⟩) = t.coefficient ∧
    polynomial ⟨t :: ts⟩ ≠ 0 := by
  simp only [leadingTerms, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hlt (u) (hu : u ∈ ts) :
      (grevlexOrder n).toSyn (exponents u.monomial) <
        (grevlexOrder n).toSyn (exponents t.monomial) :=
    (grevlexOrder_lt_iff _ _).mpr (eq_of_beq (h.2 u hu))
  have hc : coeff (exponents t.monomial) (polynomial ⟨t :: ts⟩) = t.coefficient := by
    have hz := coefficient_zero_of_absent ts (exponents t.monomial) (by
      intro u hu he
      have hh := hlt u hu
      rw [he] at hh
      exact (lt_irrefl _ hh))
    simpa [polynomial] using congrArg (fun x => t.coefficient + x) hz
  have hn : polynomial ⟨t :: ts⟩ ≠ 0 := by
    intro hz
    rw [hz, coeff_zero] at hc
    exact h.1 hc.symm
  have hd : (grevlexOrder n).degree (polynomial ⟨t :: ts⟩) = exponents t.monomial := by
    apply (grevlexOrder n).toSyn.injective
    apply le_antisymm
    · apply (grevlexOrder n).degree_le_iff.mpr
      intro e he
      obtain ⟨u, hu, rfl⟩ := support_term he
      rcases List.mem_cons.mp hu with rfl | hu
      · exact le_rfl
      · exact (hlt u hu).le
    · exact (grevlexOrder n).le_degree (mem_support_iff.mpr (hc ▸ h.1))
  exact ⟨hd, by simpa only [MonomialOrder.leadingCoeff, hd] using hc, hn⟩

variable (F : Macaulean.Algebra.CoefficientField)

private theorem normalized_empty {p : Macaulean.Polynomial F.Carrier n}
    (h : (Macaulean.M2.KernelPolynomial.normalize p).terms = []) : polynomial p = 0 := by
  rw [← worksheet_normalize F p]
  simp [polynomial, h]

theorem checked_normalized_head {p : Macaulean.Polynomial F.Carrier n}
    {t : Macaulean.PolyTerm F.Carrier n} {ts : List (Macaulean.PolyTerm F.Carrier n)}
    (hs : (Macaulean.M2.KernelPolynomial.normalize p).terms = t :: ts)
    (h : leading p = true) :
    (grevlexOrder n).degree (polynomial p) = exponents t.monomial ∧
    (grevlexOrder n).leadingCoeff (polynomial p) = t.coefficient ∧ polynomial p ≠ 0 := by
  have hp : polynomial p = polynomial ⟨t :: ts⟩ := by
    rw [← worksheet_normalize F p]
    simp only [polynomial, hs]
  rw [hp]
  apply checked_head
  simpa only [leading, hs, leadingTerms] using h

theorem checked_monic {p : Macaulean.Polynomial F.Carrier n} (h : monic p = true) :
    (grevlexOrder n).leadingCoeff (polynomial p) = 1 := by
  simp only [monic, Bool.and_eq_true] at h
  cases hs : (Macaulean.M2.KernelPolynomial.normalize p).terms with
  | nil => simp [hs] at h
  | cons t ts =>
    have hc : t.coefficient = 1 := by simpa only [hs, beq_iff_eq] using h.2
    exact (checked_normalized_head F hs h.1).2.1.trans hc

/-- A checked executable degree bound is the bound required by the remainder theorem. -/
theorem checked_degreeBound {target a b : Macaulean.Polynomial F.Carrier n}
    (ht : leading target = true) (ha : leading a = true) (hb : leading b = true)
    (h : degreeBound target a b = true) :
    (grevlexOrder n).toWithBotSyn ((grevlexOrder n).withBotDegree (polynomial a)) +
      (grevlexOrder n).toWithBotSyn ((grevlexOrder n).withBotDegree (polynomial b)) ≤
      (grevlexOrder n).toWithBotSyn ((grevlexOrder n).withBotDegree (polynomial target)) := by
  cases sa : (Macaulean.M2.KernelPolynomial.normalize a).terms with
  | nil => simp [normalized_empty F sa]
  | cons u us =>
    cases sb : (Macaulean.M2.KernelPolynomial.normalize b).terms with
    | nil => simp [normalized_empty F sb]
    | cons v vs =>
      cases st : (Macaulean.M2.KernelPolynomial.normalize target).terms with
      | nil => simp [degreeBound, sa, sb, st] at h
      | cons t ts =>
        obtain ⟨da, _, na⟩ := checked_normalized_head F sa ha
        obtain ⟨db, _, nb⟩ := checked_normalized_head F sb hb
        obtain ⟨dt, _, nt⟩ := checked_normalized_head F st ht
        rw [((grevlexOrder n).withBotDegree_eq_coe_degree_iff _).mpr na,
          ((grevlexOrder n).withBotDegree_eq_coe_degree_iff _).mpr nb,
          ((grevlexOrder n).withBotDegree_eq_coe_degree_iff _).mpr nt, da, db, dt]
        simp only [MonomialOrder.toWithBotSyn_apply_coe, ← WithBot.coe_add, WithBot.coe_le_coe]
        rw [← map_add, ← exponents_mul]
        apply le_of_not_gt
        intro hgt
        have cmp := (grevlexOrder_lt_iff _ _).mp hgt
        have flip := Macaulean.Mon.grevlex_flip.mp cmp
        simp [degreeBound, sa, sb, st, flip] at h

@[simp] theorem exponents_factor (a b : Macaulean.Mon n) :
    exponents (factor a b) = exponents b - exponents a := by
  ext i
  simp [exponents, factor]
  omega

/-- The executable S-polynomial has precisely the mathematical S-polynomial meaning. -/
theorem checked_sPolynomial {p q : Macaulean.Polynomial F.Carrier n}
    (hp : leading p = true) (hq : leading q = true) :
    polynomial (sPolynomial p q) =
      (grevlexOrder n).sPolynomial (polynomial p) (polynomial q) := by
  cases sp : (Macaulean.M2.KernelPolynomial.normalize p).terms with
  | nil => simp [sPolynomial, sp, normalized_empty F sp]
  | cons t ts =>
    cases sq : (Macaulean.M2.KernelPolynomial.normalize q).terms with
    | nil => simp [sPolynomial, sp, sq, normalized_empty F sq]
    | cons u us =>
      obtain ⟨dp, cp, _⟩ := checked_normalized_head F sp hp
      obtain ⟨dq, cq, _⟩ := checked_normalized_head F sq hq
      simp only [sPolynomial, sp, sq, worksheet_sub, worksheet_mul,
        MonomialOrder.sPolynomial, dp, dq, cp, cq]
      simp [polynomial]

private theorem linearCombination_value (row basis : List (Macaulean.Polynomial F.Carrier n)) :
    polynomial (Macaulean.Algebra.Certificates.linearCombination row basis) =
      ((row.zip basis).map (fun (a,b) => polynomial a * polynomial b)).sum := by
  induction row generalizing basis with
  | nil => simp [Macaulean.Algebra.Certificates.linearCombination]
  | cons a row ih =>
    cases basis with
    | nil => simp [Macaulean.Algebra.Certificates.linearCombination]
    | cons b basis =>
      simp [Macaulean.Algebra.Certificates.linearCombination, worksheet_add, worksheet_mul, ih]

private theorem sum_zip_index (row basis : List (Macaulean.Polynomial F.Carrier n))
    (hlen : row.length = basis.length) :
    ((row.zip basis).map (fun (a,b) => polynomial a * polynomial b)).sum =
      ∑ i : Fin basis.length, polynomial (row[i.val]'(by simpa only [hlen] using i.isLt)) *
        polynomial basis[i] := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    simp [List.getElem_zip]

/-- An accepted row yields the bounded representation used by Buchberger's criterion. -/
def checked_row {target : Macaulean.Polynomial F.Carrier n}
    {basis row : List (Macaulean.Polynomial F.Carrier n)}
    (hb : ∀ b ∈ basis, leading b = true)
    (hr : Macaulean.Algebra.Certificates.represents target basis row = true)
    (hd : boundedRow target basis row = true) :
    BoundedRepresentation (grevlexOrder n) (fun i : Fin basis.length => polynomial basis[i])
      (polynomial target) := by
  have len := Macaulean.Algebra.Certificates.represents_dimension hr
  simp only [boundedRow, Bool.and_eq_true, List.all_eq_true] at hd
  refine ⟨fun i => polynomial (row[i.val]'(by simpa only [len] using i.isLt)), ?_, ?_⟩
  · rw [← sum_zip_index F row basis len, ← linearCombination_value F]
    simp only [Macaulean.Algebra.Certificates.represents, Bool.and_eq_true] at hr
    exact worksheet_equivalent F (Macaulean.Algebra.Certificates.equal_sound hr.2)
  · intro i
    have hm : (row[i.val]'(by simpa only [len] using i.isLt), basis[i]) ∈ row.zip basis := by
      have hi : i.val < (row.zip basis).length := by simp [len]
      simpa only [List.getElem_zip, Fin.getElem_fin] using List.getElem_mem (l := row.zip basis) (n := i.val) hi
    have ha := hd.1.2 (row[i.val]'(by simpa only [len] using i.isLt)) (List.getElem_mem ..)
    have hh := checked_degreeBound F hd.1.1.2 ha (hb basis[i] (List.getElem_mem ..)) (hd.2 _ hm)
    simpa only [add_comm] using hh

/-- The finite matrix checker implies the actual leading-term-ideal Gröbner property. -/
theorem checkBasis_sound {basis : List (Macaulean.Polynomial F.Carrier n)}
    {rows : List (List (List (Macaulean.Polynomial F.Carrier n)))}
    (h : checkBasis basis rows = true) :
    (grevlexOrder n).IsGroebnerBasis
      (Set.range (fun i : Fin basis.length => polynomial basis[i]))
      (Ideal.span (Set.range (fun i : Fin basis.length => polynomial basis[i]))) := by
  simp only [checkBasis, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  have hl : ∀ b ∈ basis, leading b = true := by
    intro b hb
    have hh := h.1.1 b hb
    simp only [monic, Bool.and_eq_true] at hh
    exact hh.1
  apply BuchbergerCertificate.isGroebnerBasis
  refine ⟨fun i => checked_monic F (h.1.1 _ (List.getElem_mem ..)), ?_⟩
  intro i j
  have hh := h.2 i j
  simp only [pair, Bool.and_eq_true] at hh
  have c := checked_row F hl hh.1 hh.2
  rw [checked_sPolynomial F (p := basis[i]) (q := basis[j])
    (hl _ (List.getElem_mem ..)) (hl _ (List.getElem_mem ..))] at c
  exact c

end
end Macaulean.Verification.Mathlib
