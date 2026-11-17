import Macaulean.Interpreter.GCD.Interface

namespace Macaulean.M2.GCD.Execution
open Macaulean.M2.Runtime Univariate

private theorem degree_fold_ge (p : Polynomials.Raw) (acc : Nat) :
    acc ≤ p.foldl (fun d t => max d t.2.sum) acc := by
  induction p generalizing acc with
  | nil => exact Nat.le_refl _
  | cons t ts ih =>
    exact Nat.le_trans (Nat.le_max_left acc t.2.sum) (ih _)

theorem rank_le_degree (p : Poly) : rank p ≤ degree (Polynomials.encode p)+1 := by
  cases p with
  | mk ts =>
    cases ts with
    | nil => simp [rank, degree, Polynomials.encode]
    | cons t ts =>
      have h := degree_fold_ge (Polynomials.encode (⟨ts⟩ : Poly)) (max 0 t.monomial.powers.sum)
      simp only [powers_singleton, List.sum_cons, List.sum_nil, Nat.add_zero,
        Nat.zero_max] at h
      change t.monomial.degree + 1 ≤
        (Polynomials.encode (⟨ts⟩ : Poly)).foldl (fun d t => max d t.2.sum)
          (max 0 t.monomial.powers.sum) + 1
      simpa only [powers_singleton, List.sum_cons, List.sum_nil, Nat.add_zero,
        Nat.zero_max] using Nat.add_le_add_right h 1

theorem input_fuel_sufficient (p g : Poly) :
    64 * (max (rank p) (rank g)+1) + 8*rank g + 203 ≤
      fuel (Polynomials.encode p) (Polynomials.encode g) := by
  have hp := rank_le_degree p
  have hg := rank_le_degree g
  unfold fuel fuelForDegree
  omega

theorem compute_correct_canonical (id : Nat) (name : String) (p g : Poly)
    (hp : Canonical p.terms) (hg : Canonical g.terms) :
    ∃ out, Canonical out.terms ∧ MonicOrZero out ∧
      TotalCorrectness.IsGCD Divides p g out ∧
      compute (value id name p) (value id name g) = .ok (value id name out) := by
  have hin := gcd_inputs_canonical id name p g hp hg
  have hdata : Polynomials.callPrimitive .gcdInputs
      (.sequence [value id name p,value id name g]) =
      .ok (.list [value id name p,value id name g]) := by
    simp only [Polynomials.callPrimitive, hin, bind, Except.bind, pure, Except.pure]
    rfl
  obtain ⟨out,after,ho,hm,hgcd,_,run⟩ := gcd_entry_correct id name
    (.sequence [value id name p,value id name g]) p g hp hg hdata {}
    prelude_globals (by rfl) _ (input_fuel_sufficient p g)
  refine ⟨out,ho,hm,hgcd,?_⟩
  simp only [compute, hin, bind, Except.bind]
  change (do
    let (result,_) ← finish (call (fuel (Polynomials.encode p) (Polynomials.encode g))
      (.algebra (.library "gcd")) (.sequence [value id name p,value id name g]) {})
    pure result) = _
  rw [run]
  rfl

theorem compute_correct_validated (id : Nat) (name : String) (f g : Value) (p q : Poly)
    (hp : Canonical p.terms) (hq : Canonical q.terms)
    (hin : Polynomials.gcdInputs (.sequence [f,g]) =
      .ok (ringInfo id name,Polynomials.encode p,Polynomials.encode q)) :
    ∃ out, Canonical out.terms ∧ MonicOrZero out ∧
      TotalCorrectness.IsGCD Divides p q out ∧
      compute f g = .ok (value id name out) := by
  obtain ⟨out,ho,hm,hgcd,hcompute⟩ := compute_correct_canonical id name p q hp hq
  refine ⟨out,ho,hm,hgcd,?_⟩
  have heq : compute f g = compute (value id name p) (value id name q) := by
    simp only [compute, hin, gcd_inputs_canonical id name p q hp hq]
  exact heq.trans hcompute

theorem normalized_has_canonical (raw out : Polynomials.Raw)
    (h : Polynomials.normalized 1 raw = .ok out) :
    ∃ p : Poly, Canonical p.terms ∧ Polynomials.encode p = out := by
  cases hd : Polynomials.decode 1 raw with
  | error e => simp [Polynomials.normalized, hd, Functor.map, Except.map] at h
  | ok p =>
    simp [Polynomials.normalized, hd, Functor.map, Except.map] at h
    exact ⟨KernelPolynomial.normalize p,normalize_canonical _,h⟩

theorem as_polynomial_has_canonical (v : Value) (id : Nat) (name : String) (raw : Polynomials.Raw)
    (h : Polynomials.asPolynomial v = .ok (ringInfo id name,raw)) :
    ∃ p : Poly, Canonical p.terms ∧ Polynomials.encode p = raw := by
  cases v <;> try (simp [Polynomials.asPolynomial] at h)
  rename_i object
  cases object <;> try (simp [Polynomials.asPolynomial] at h)
  rename_i r input
  cases hn : Polynomials.normalized r.names.length input with
  | error e => simp [Polynomials.asPolynomial, hn, Polynomials.liftError, Except.mapError, Functor.map, Except.map] at h
  | ok output =>
    simp [Polynomials.asPolynomial, hn, Polynomials.liftError, Except.mapError, Functor.map, Except.map] at h
    obtain ⟨hr,ho⟩ := h
    subst r
    subst output
    exact normalized_has_canonical input raw hn

theorem validated_has_canonical (f g : Value)
    (data : Polynomials.RingInfo × Polynomials.Raw × Polynomials.Raw)
    (valid : Polynomials.gcdInputs (.sequence [f,g]) = .ok data) :
    ∃ (id : Nat) (name : String) (p q : Poly), Canonical p.terms ∧ Canonical q.terms ∧
      Polynomials.gcdInputs (.sequence [f,g]) =
        .ok (ringInfo id name,Polynomials.encode p,Polynomials.encode q) := by
  cases hf : Polynomials.asPolynomial f with
  | error e => simp [Polynomials.gcdInputs, Polynomials.binaryArgs, Polynomials.unpack, bind, Except.bind, pure, Except.pure, hf] at valid
  | ok a =>
    obtain ⟨r,rawp⟩ := a
    cases hg : Polynomials.asPolynomial g with
    | error e => simp [Polynomials.gcdInputs, Polynomials.binaryArgs, Polynomials.unpack, bind, Except.bind, pure, Except.pure, hf, hg] at valid
    | ok b =>
      obtain ⟨s,rawq⟩ := b
      by_cases hrs : r = s
      · subst s
        by_cases hlen : r.names.length = 1
        · obtain ⟨name, hnames⟩ : ∃ name, r.names = [name] := by
            cases hn : r.names with
            | nil => simp [hn] at hlen
            | cons name rest =>
              cases rest with
              | nil => exact ⟨name,rfl⟩
              | cons x xs => simp [hn] at hlen
          have hr : r = ringInfo r.id name := by cases r; simp_all [ringInfo]
          obtain ⟨p,hp,hep⟩ := as_polynomial_has_canonical f r.id name rawp (by rw [← hr]; exact hf)
          obtain ⟨q,hq,heq⟩ := as_polynomial_has_canonical g r.id name rawq (by rw [← hr]; exact hg)
          refine ⟨r.id,name,p,q,hp,hq,?_⟩
          rw [hep, heq, ← hr]
          simp [Polynomials.gcdInputs, Polynomials.binaryArgs, Polynomials.unpack, bind, Except.bind, pure, Except.pure,
            hf, hg, hlen]
        · simp [Polynomials.gcdInputs, Polynomials.binaryArgs, Polynomials.unpack, bind, Except.bind, pure, Except.pure, hf, hg, hlen] at valid
      · simp [Polynomials.gcdInputs, Polynomials.binaryArgs, Polynomials.unpack, bind, Except.bind, pure, Except.pure, hf, hg, hrs] at valid

/-- Every input accepted by the production validator succeeds and returns a
monic GCD of the validated polynomials, with no separate fuel assumption. -/
theorem compute_total (f g : Value)
    (valid : ∃ data, Polynomials.gcdInputs (.sequence [f,g]) = .ok data) :
    ∃ (id : Nat) (name : String) (p q out : Poly), Canonical p.terms ∧ Canonical q.terms ∧
      Polynomials.gcdInputs (.sequence [f,g]) =
        .ok (ringInfo id name,Polynomials.encode p,Polynomials.encode q) ∧
      Canonical out.terms ∧ MonicOrZero out ∧ TotalCorrectness.IsGCD Divides p q out ∧
      compute f g = .ok (value id name out) := by
  obtain ⟨data,valid⟩ := valid
  obtain ⟨id,name,p,q,hp,hq,hin⟩ := validated_has_canonical f g data valid
  obtain ⟨out,ho,hm,hgcd,run⟩ := compute_correct_validated id name f g p q hp hq hin
  exact ⟨id,name,p,q,out,hp,hq,hin,ho,hm,hgcd,run⟩

end Macaulean.M2.GCD.Execution
