import Macaulean.Interpreter.KernelPolynomialWeights

/-!
Structural facts about the production sparse polynomial representation in one
variable. These prove facts about `KernelPolynomial.normalize` itself, rather
than assuming a canonical representation for the arithmetic used by the DSL.
-/
namespace Macaulean.M2.GCD.Univariate
open Macaulean KernelPolynomial Lean.Grind

abbrev Term := PolyTerm Rat 1
abbrev Poly := Polynomial Rat 1

theorem powers_singleton (m : Mon 1) : m.powers = [m.degree] := by
  rcases m with ⟨powers, h⟩
  cases powers with
  | nil => simp at h
  | cons k ks =>
    have : ks = [] := by simpa using h
    subst ks
    rfl

theorem mon_eq_of_degree_eq {m n : Mon 1} (h : m.degree = n.degree) : m = n := by
  apply (Mon.powers_eq_iff_eq).mp
  rw [powers_singleton, powers_singleton, h]

theorem grevlex_degree (m n : Mon 1) :
    m.grevlex n = compare m.degree n.degree := by
  unfold Mon.grevlex
  by_cases h : m.degree = n.degree
  · have hm := mon_eq_of_degree_eq h
    subst n
    simp
  · cases hc : compare m.degree n.degree <;> simp_all

theorem degree_mul (m n : Mon 1) : (m.mul n).degree = m.degree + n.degree := by
  simp only [Mon.degree, Mon.mul]
  rw [powers_singleton m, powers_singleton n]
  simp [Mon.degree]

/-- All represented degrees are below a strict upper bound. -/
def Below (bound : Nat) (ts : List Term) : Prop :=
  ∀ t ∈ ts, t.monomial.degree < bound

theorem below_nil (n : Nat) : Below n [] := by simp [Below]

theorem below_cons (n : Nat) (t : Term) (ts : List Term) :
    Below n (t :: ts) ↔ t.monomial.degree < n ∧ Below n ts := by
  simp [Below]

theorem below_mono {a b : Nat} {ts : List Term} (h : Below a ts) (hab : a ≤ b) :
    Below b ts := by
  intro t ht
  have := h t ht
  omega

/-- Canonical sparse data: nonzero terms in strictly decreasing degree order. -/
inductive Canonical : List Term → Prop
  | nil : Canonical []
  | cons {t : Term} {ts : List Term} :
      t.coefficient ≠ 0 → Below t.monomial.degree ts → Canonical ts →
      Canonical (t :: ts)

theorem insert_below {bound : Nat} {t : Term} {ts : List Term}
    (ht : t.monomial.degree < bound) (hs : Below bound ts) :
    Below bound (insert t ts) := by
  induction ts with
  | nil =>
    simp only [KernelPolynomial.insert]
    split
    · exact below_nil _
    · exact (below_cons ..).mpr ⟨ht, below_nil _⟩
  | cons u us ih =>
    obtain ⟨hu, hus⟩ := (below_cons ..).mp hs
    simp only [KernelPolynomial.insert]
    split
    · split
      · exact hs
      · exact (below_cons ..).mpr ⟨ht, hs⟩
    · split
      · exact hus
      · exact (below_cons ..).mpr ⟨hu, hus⟩
    · exact (below_cons ..).mpr ⟨hu, ih hus⟩

theorem insert_canonical (t : Term) {ts : List Term} (hs : Canonical ts) :
    Canonical (insert t ts) := by
  induction hs with
  | nil =>
    simp only [KernelPolynomial.insert]
    split
    · exact .nil
    · exact .cons ‹_› (below_nil _) .nil
  | @cons u us hu hbelow hcanon ih =>
    simp only [KernelPolynomial.insert, grevlex_degree]
    split
    · next h =>
      have hdegree : u.monomial.degree < t.monomial.degree :=
        Nat.compare_eq_gt.mp h
      split
      · exact .cons hu hbelow hcanon
      · apply Canonical.cons ‹_›
        · exact (below_cons ..).mpr ⟨hdegree, below_mono hbelow (by omega)⟩
        · exact .cons hu hbelow hcanon
    · split
      · exact hcanon
      · exact .cons ‹_› hbelow hcanon
    · next h =>
      have hdegree : t.monomial.degree < u.monomial.degree :=
        Nat.compare_eq_lt.mp h
      exact .cons hu (insert_below hdegree hbelow) ih

theorem fold_insert_canonical (ts acc : List Term) (ha : Canonical acc) :
    Canonical (ts.foldl (fun xs t => insert t xs) acc) := by
  induction ts generalizing acc with
  | nil => exact ha
  | cons t ts ih => exact ih _ (insert_canonical t ha)

theorem normalize_canonical (p : Poly) : Canonical (normalize p).terms :=
  fold_insert_canonical p.terms [] .nil

theorem fold_insert_below (ts acc : List Term) (bound : Nat)
    (ht : Below bound ts) (ha : Below bound acc) :
    Below bound (ts.foldl (fun xs t => insert t xs) acc) := by
  induction ts generalizing acc with
  | nil => exact ha
  | cons t ts ih =>
    obtain ⟨hhead, htail⟩ := (below_cons ..).mp ht
    exact ih _ htail (insert_below hhead ha)

theorem normalize_below (p : Poly) (bound : Nat) (h : Below bound p.terms) :
    Below bound (normalize p).terms :=
  fold_insert_below p.terms [] bound h (below_nil _)

/-- Coefficient observation on arbitrary sparse data, including duplicates. -/
def coeff (ts : List Term) (k : Nat) : Rat :=
  weightedSum (fun m => if m.degree = k then 1 else 0) ts

theorem coeff_nil (k : Nat) : coeff [] k = 0 := rfl

theorem coeff_cons (t : Term) (ts : List Term) (k : Nat) :
    coeff (t :: ts) k =
      (if t.monomial.degree = k then t.coefficient else 0) + coeff ts k := by
  simp only [coeff, weightedSum]
  split <;> grind

theorem coeff_below {ts : List Term} {bound k : Nat}
    (hs : Below bound ts) (hk : bound ≤ k) : coeff ts k = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨ht, htail⟩ := (below_cons ..).mp hs
    rw [coeff_cons, if_neg (by omega), ih htail]
    grind

theorem coeff_mem {ts : List Term} (hs : Canonical ts) {t : Term}
    (ht : t ∈ ts) : coeff ts t.monomial.degree = t.coefficient := by
  induction hs with
  | nil => simp at ht
  | @cons u us hu hb hc ih =>
    rcases List.mem_cons.mp ht with heq | hmem
    · subst t
      rw [coeff_cons, if_pos rfl, coeff_below hb (Nat.le_refl _)]
      grind
    · have hlt := hb t hmem
      rw [coeff_cons, if_neg (by omega), ih hmem]
      grind

theorem canonical_below_head {t : Term} {ts : List Term}
    (hs : Canonical (t :: ts)) : Below (t.monomial.degree + 1) (t :: ts) := by
  cases hs with
  | cons _ hb _ =>
    exact (below_cons ..).mpr ⟨by omega, below_mono hb (by omega)⟩

theorem canonical_ext {ps qs : List Term} (hp : Canonical ps) (hq : Canonical qs)
    (h : ∀ k, coeff ps k = coeff qs k) : ps = qs := by
  induction hp generalizing qs with
  | nil =>
    cases hq with
    | nil => rfl
    | @cons u us hu hb hc =>
      have hm := coeff_mem (Canonical.cons hu hb hc) List.mem_cons_self
      have he := h u.monomial.degree
      rw [coeff_nil, hm] at he
      exact False.elim (hu he.symm)
  | @cons t ts ht hb hc ih =>
    cases hq with
    | nil =>
      have hm := coeff_mem (Canonical.cons ht hb hc) List.mem_cons_self
      have he := h t.monomial.degree
      rw [coeff_nil, hm] at he
      exact False.elim (ht he)
    | @cons u us hu hub huc =>
      have hpc := Canonical.cons ht hb hc
      have hqc := Canonical.cons hu hub huc
      have hdeg : t.monomial.degree = u.monomial.degree := by
        have hphead := coeff_mem hpc List.mem_cons_self
        have hqhead := coeff_mem hqc List.mem_cons_self
        have hplim := canonical_below_head hpc
        have hqlim := canonical_below_head hqc
        by_cases hlt : t.monomial.degree < u.monomial.degree
        · have hz := coeff_below hplim (by omega : t.monomial.degree + 1 ≤ u.monomial.degree)
          have he := h u.monomial.degree
          rw [hz, hqhead] at he
          exact False.elim (hu he.symm)
        · by_cases hgt : u.monomial.degree < t.monomial.degree
          · have hz := coeff_below hqlim (by omega : u.monomial.degree + 1 ≤ t.monomial.degree)
            have he := h t.monomial.degree
            rw [hz, hphead] at he
            exact False.elim (ht he)
          · omega
      have hm := mon_eq_of_degree_eq hdeg
      have hco : t.coefficient = u.coefficient := by
        have hphead := coeff_mem hpc List.mem_cons_self
        have hqhead := coeff_mem hqc List.mem_cons_self
        have he := h t.monomial.degree
        rw [hphead, hdeg, hqhead] at he
        exact he
      have heq : t = u := by cases t; cases u; simp_all
      subst u
      congr 1
      apply ih huc
      intro k
      have he := h k
      rw [coeff_cons, coeff_cons] at he
      grind

theorem coeff_normalize (p : Poly) (k : Nat) :
    coeff (normalize p).terms k = coeff p.terms k :=
  weightedSum_normalize _ p

theorem normalize_eq_self (p : Poly) (h : Canonical p.terms) :
    normalize p = p := by
  have he := canonical_ext (normalize_canonical p) h (coeff_normalize p)
  exact congrArg (fun terms => (⟨terms⟩ : Poly)) he

theorem normalize_idempotent (p : Poly) : normalize (normalize p) = normalize p :=
  normalize_eq_self _ (normalize_canonical p)

theorem canonical_nonzero {ts : List Term} (hc : Canonical ts) {t : Term}
    (ht : t ∈ ts) : t.coefficient ≠ 0 := by
  induction hc with
  | nil => simp at ht
  | cons h _ _ ih =>
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h
    · exact ih ht

/-- Cancelling the top coefficient lowers the bound of a canonical result. -/
theorem below_of_top_coeff_zero {ts : List Term} {k : Nat}
    (hc : Canonical ts) (hb : Below (k+1) ts) (hz : coeff ts k = 0) :
    Below k ts := by
  intro t ht
  have hd := hb t ht
  have hm := coeff_mem hc ht
  have hn := canonical_nonzero hc ht
  by_cases he : t.monomial.degree = k
  · rw [he, hz] at hm
    exact False.elim (hn hm.symm)
  · omega

theorem sub_canonical (p q : Poly) : Canonical (KernelPolynomial.sub p q).terms :=
  normalize_canonical _

theorem sub_below (p q : Poly) (bound : Nat)
    (hp : Below bound p.terms) (hq : Below bound q.terms) :
    Below bound (KernelPolynomial.sub p q).terms := by
  apply normalize_below
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hq u hu

theorem coeff_sub (p q : Poly) (k : Nat) :
    coeff (KernelPolynomial.sub p q).terms k = coeff p.terms k - coeff q.terms k :=
  weightedSum_sub _ p q

/-- A single term before normalization; zero coefficients are permitted. -/
def monomial (c : Rat) (k : Nat) : Poly := ⟨[⟨c,⟨[k],rfl⟩⟩]⟩

theorem mul_monomial_below (c : Rat) (k bound : Nat) (p : Poly)
    (hp : Below bound p.terms) :
    Below (k + bound) (KernelPolynomial.mul (monomial c k) p).terms := by
  apply normalize_below
  simp only [monomial, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  have hd := hp u hu
  simp only [degree_mul]
  change k + u.monomial.degree < k + bound
  omega

theorem coeff_mul_monomial (c : Rat) (k j : Nat) (p : Poly) :
    coeff (KernelPolynomial.mul (monomial c k) p).terms (k+j) = c * coeff p.terms j := by
  unfold coeff
  rw [weightedSum_mul]
  simp only [monomial, weightedSum, degree_mul]
  have hdeg : (⟨[k],rfl⟩ : Mon 1).degree = k := rfl
  simp only [hdeg, Nat.add_left_cancel_iff]
  grind

/-- The coefficient/monomial quotient used to cancel the leading term. -/
def cancellationTerm (t u : Term) : Poly :=
  monomial (t.coefficient / u.coefficient) (t.monomial.degree - u.monomial.degree)

/-- A real leading-term subtraction in the production arithmetic lowers degree.
This is the algebraic descent fact needed by source-language polynomial division. -/
theorem cancellation_decreases {t u : Term} {ts us : List Term}
    (hp : Canonical (t :: ts)) (hq : Canonical (u :: us))
    (hdegree : u.monomial.degree ≤ t.monomial.degree) :
    Below t.monomial.degree
      (KernelPolynomial.sub ⟨t :: ts⟩
        (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)).terms := by
  have hd : t.monomial.degree - u.monomial.degree + u.monomial.degree =
      t.monomial.degree := by omega
  apply below_of_top_coeff_zero (sub_canonical ..)
  · apply sub_below
    · exact canonical_below_head hp
    · have hm := mul_monomial_below (t.coefficient/u.coefficient)
        (t.monomial.degree-u.monomial.degree) (u.monomial.degree+1)
        ⟨u :: us⟩ (canonical_below_head hq)
      simpa only [cancellationTerm, ← Nat.add_assoc, hd] using hm
  · rw [coeff_sub]
    have hprod := coeff_mul_monomial (t.coefficient/u.coefficient)
      (t.monomial.degree-u.monomial.degree) u.monomial.degree ⟨u :: us⟩
    rw [hd] at hprod
    rw [coeff_mem hp List.mem_cons_self]
    change t.coefficient -
      coeff (KernelPolynomial.mul (monomial (t.coefficient/u.coefficient)
        (t.monomial.degree-u.monomial.degree)) ⟨u :: us⟩).terms t.monomial.degree = 0
    rw [hprod, coeff_mem hq List.mem_cons_self,
      Rat.div_mul_cancel (canonical_nonzero hq List.mem_cons_self)]
    grind

/-- Degree plus one on a nonzero canonical polynomial, and zero on zero. -/
def rank (p : Poly) : Nat :=
  match p.terms with
  | [] => 0
  | t :: _ => t.monomial.degree + 1

theorem rank_le_of_below {p : Poly} {bound : Nat} (h : Below bound p.terms) :
    rank p ≤ bound := by
  cases p with
  | mk ts =>
    cases ts with
    | nil => exact Nat.zero_le _
    | cons t ts =>
      have hd := (below_cons ..).mp h
      change t.monomial.degree + 1 ≤ bound
      omega

theorem cancellation_rank_lt {t u : Term} {ts us : List Term}
    (hp : Canonical (t :: ts)) (hq : Canonical (u :: us))
    (hdegree : u.monomial.degree ≤ t.monomial.degree) :
    rank (KernelPolynomial.sub ⟨t :: ts⟩
      (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)) < rank ⟨t :: ts⟩ := by
  have := rank_le_of_below (cancellation_decreases hp hq hdegree)
  change _ < t.monomial.degree + 1
  omega

theorem polynomial_ext {p q : Poly} (hp : Canonical p.terms) (hq : Canonical q.terms)
    (h : ∀ k, coeff p.terms k = coeff q.terms k) : p = q :=
  congrArg (fun terms => (⟨terms⟩ : Poly)) (canonical_ext hp hq h)

/-- The other branch of ordered division removes an irreducible leading term.
The real subtraction returns exactly the remaining canonical tail. -/
theorem sub_head {t : Term} {ts : List Term} (hp : Canonical (t :: ts)) :
    KernelPolynomial.sub ⟨t :: ts⟩ ⟨[t]⟩ = ⟨ts⟩ := by
  cases hp with
  | cons _ _ hc =>
    apply polynomial_ext (sub_canonical ..) hc
    intro k
    rw [coeff_sub, coeff_cons, coeff_cons, coeff_nil]
    grind

theorem sub_head_rank_lt {t : Term} {ts : List Term}
    (hp : Canonical (t :: ts)) :
    rank (KernelPolynomial.sub ⟨t :: ts⟩ ⟨[t]⟩) < rank ⟨t :: ts⟩ := by
  rw [sub_head hp]
  cases hp with
  | cons _ hb _ =>
    have := rank_le_of_below hb
    change _ < t.monomial.degree + 1
    omega

end Macaulean.M2.GCD.Univariate
