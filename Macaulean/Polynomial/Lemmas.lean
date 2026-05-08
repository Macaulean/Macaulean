import Macaulean.Polynomial.Basic
import Lean
open Lean Grind CommRing

namespace Macaulean

namespace Mon


/-! ## Lemmas about grevlex -/
@[simp]
theorem eq_of_grevlex {m1 m2 : Mon n} : (m1.grevlex m2 = .eq) ↔ m1 = m2 := by
  constructor
  case mp =>
    exact Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex)
  case mpr =>
    simp

@[simp]
theorem grevlex_rfl {m : Mon n} : m.grevlex m = .eq :=
  by simp

theorem grevlex_trans {m1 m2 m3 : Mon n} (h1 : m1.grevlex m2 = .gt) (h2 : m2.grevlex m3 = .gt) :
    m1.grevlex m3 = .gt := by
  simp [Mon.grevlex, Ordering.then_eq_gt] at *
  cases h1
  case inl hdeg1=>
    cases h2
    case inl hdeg2 =>
      left
      exact Std.TransCmp.gt_trans hdeg1 hdeg2
    case inr heq =>
      left
      simp [heq.1] at hdeg1
      trivial
  case inr heq =>
    simp [heq.1]
    cases h2
    case inl hdeg2 =>
      left
      trivial
    case inr heq2 =>
      simp [heq2.1]
      exact Std.TransCmp.lt_trans heq.2 heq2.2

theorem grevlex_swap (m₁ m₂ : Mon n) :
    (Mon.grevlex m₁ m₂).swap = Mon.grevlex m₂ m₁ :=
    Eq.symm (inferInstance : Std.OrientedCmp (grevlex (n := n))).1

theorem grevlex_flip {m₁ m₂ : Mon n} :
  m₁.grevlex m₂ = .lt ↔ m₂.grevlex m₁ = .gt := by
  constructor
  case mp =>
    intro h
    have := grevlex_swap m₁ m₂; rw [h] at this; simpa using this.symm
  case mpr =>
    intro h
    have := grevlex_swap m₂ m₁; rw [h] at this; simpa using this.symm

private theorem degree_mul {m1 m2 : Mon n} : (m1.mul m2).degree = m1.degree + m2.degree := by
  simp [Mon.mul, Mon.degree]
  generalize h1 : m1.powers = m1p, h2 : m2.powers = m2p
  have lengthHyp : m1p.length = m2p.length := by
    rw [← h1, ← h2]
    simp [m1.powers_length, m2.powers_length]
  clear h1 h2
  induction m1p generalizing m2p
  case nil =>
    symm at lengthHyp
    simp [List.length_eq_zero_iff] at lengthHyp
    simp [lengthHyp]
  case cons head1 tail1 ih =>
    cases m2p
    case nil => contradiction
    case cons head2 tail2 =>
      simp [List.length_cons] at lengthHyp
      simp [ih, lengthHyp]
      ac_nf

/-- Monotonicity of grevlex under monomial multiplication -/
private theorem grevlex_mul_mono {m₁ m₂ m : Mon n}
    : m₁.Grevlex m₂ ↔ (m.mul m₁).Grevlex (m.mul m₂) := by
  simp [Mon.Grevlex, degree_mul]
  constructor
  case mp =>
    intro h
    cases h
    case inl hdeg =>
      left
      trivial
    case inr hNext =>
      right
      have ⟨hdeg, hlex⟩ := hNext
      refine ⟨ hdeg, ?_⟩
      sorry
  case mpr =>
    intro h
    sorry

/-! ## Denotational Lemmas for monomials -/
theorem degree_unit_iff (m : Mon n) : m.degree = 0 ↔ m = unit := by
  constructor
  case mp =>
    simp [degree,List.sum_eq_zero_iff_forall_eq_nat]
    intro elemHyp
    suffices h : m.powers = List.replicate m.powers.length 0 by
      rw [m.powers_length] at h
      simp [unit,← h]
    apply List.eq_replicate_of_mem elemHyp
  case mpr =>
    intro h
    simp [h,unit,degree]

variable {R : Type} [CommRing R]

theorem denote_unit (ctx : Context R) : unit.denote (n := n) ctx = 1 := by
  simp only [denote]
  suffices h : (List.mapIdx (fun i k => ctx.get i ^ k) (unit.powers (n := n))) = List.replicate n (1 : R)
    by
      simp [h]
      clear h
      induction n
      case zero => trivial
      case succ ih =>
        simp [List.replicate_succ, Semiring.mul_one]
        apply ih
  simp [unit]
  induction n
  case zero => trivial
  case succ ih => simp [List.replicate_succ', Semiring.pow_zero, ih]

theorem denote_mulVarPower (ctx : Context R) (m : Mon n) (i : Fin n) (k : Nat)
  : denote (n := n) ctx (m.mulVarPower i k) = (ctx[i])^k * m.denote (n := n) ctx:= by
  sorry

theorem denote_fromVarPower (ctx : Context R) (m : Mon n) (i : Fin n) (k : Nat)
  : denote ctx (.fromVarPower i k) = (ctx[i])^k := by
  sorry

theorem denote_fromVar (ctx : Context R) (m : Mon n) (i : Fin n)
  : denote ctx (.fromVar i) = ctx[i] := by
  sorry

theorem denote_mul {ctx : Context R} {m1 m2 : Mon n}
  : (m1.mul m2).denote ctx = m1.denote ctx * m2.denote ctx := by
  simp only [Mon.mul, Mon.denote]
  sorry
end Mon

namespace Polynomial
variable {R : Type} [inst : Grind.CommRing R]
/-! ## Simp Lemmas for insertTerm -/

@[simp]
theorem insertTerm_nil (x : PolyTerm R n) : insertTerm x [] = [x] := by
  simp [insertTerm]

@[simp]
theorem insertTerm_cons_grevlex (x y : PolyTerm R n) (ys : List (PolyTerm R n))
  (h : x.monomial.Grevlex y.monomial)
  : insertTerm x (y :: ys) = x :: y :: ys := by
  simp [Mon.grevlex_iff_grevlex_gt] at h
  simp [insertTerm, h]

@[simp]
theorem insertTerm_cons_eq (x y : PolyTerm R n) (ys : List (PolyTerm R n))
  (h : x.monomial = y.monomial)
  : insertTerm x (y :: ys) = ⟨x.coefficient + y.coefficient, x.monomial⟩ :: ys := by
  simp [insertTerm, h]

@[simp]
theorem insertTerm_cons_grevlex_rev (x y : PolyTerm R n) (ys : List (PolyTerm R n))
  (h : y.monomial.Grevlex x.monomial)
  : insertTerm x (y :: ys) = y :: insertTerm x ys := by
  simp [Mon.grevlex_iff_grevlex_gt, ← Ordering.swap_eq_lt, Mon.grevlex_swap] at h
  simp [insertTerm, h]

/-! ## Simp Lemmas for mergeTerms -/
@[simp]
theorem mergeTerms_nil_left (xs : List (PolyTerm R n)) :
    mergeTerms [] xs = xs := by simp [mergeTerms]

@[simp]
theorem mergeTerms_nil_right (xs : List (PolyTerm R n)) :
    mergeTerms xs [] = xs := by
  induction xs
  case nil =>
    simp
  case cons head tail ih =>
    unfold mergeTerms mergeTerms.takeTillGE
    simp [ih]

theorem mergeTerms_symm (xs ys : List (PolyTerm R n)) : mergeTerms xs ys = mergeTerms ys xs := by
  induction xs generalizing ys
  case nil =>
    simp
  case cons head tail ih =>
    induction ys
    case nil =>
      simp
    case cons yhead ytail ih2 =>
      unfold mergeTerms mergeTerms.takeTillGE
      simp
      cases h : head.monomial.grevlex yhead.monomial
      case lt =>
        simp [Mon.grevlex_flip.mp h, ← ih2, mergeTerms]
      case eq =>
        simp at h
        simp [h, Semiring.add_comm, ih]
      case gt =>
        simp [Mon.grevlex_flip.mpr h, ih, mergeTerms]

@[simp]
theorem mergeTerms_singleton_left (x : PolyTerm R n) (ys : List (PolyTerm R n)) :
    mergeTerms [x] ys = insertTerm x ys := by
  induction ys
  case nil =>
    simp
  case cons head tail ih =>
    unfold mergeTerms insertTerm
    simp [mergeTerms.takeTillGE]
    congr
    funext
    congr
    simp [← ih, mergeTerms]

@[simp]
theorem mergeTerms_singleton_right (y : PolyTerm R n) (xs : List (PolyTerm R n)) :
    mergeTerms xs [y] = insertTerm y xs := by
  rw [mergeTerms_symm]
  simp

section Theorems
-- variable [deceq : DecidableEq R] [lawfuleq : LawfulBEq R]
open Grind.Semiring Grind.Ring Grind.CommSemiring
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast

/-! ## Sortedness preservation -/

private theorem Sorted_tail {t : PolyTerm R n} {ts : List (PolyTerm R n)}
    (h : Sorted (t :: ts)) : Sorted ts := (List.pairwise_cons.mp h).2

private theorem Sorted_head_grevlex_all :
    ∀ (ts : List (PolyTerm R n)) (t : PolyTerm R n),
    Sorted (t :: ts) → ∀ t' ∈ ts, t.monomial.Grevlex t'.monomial := by
  intro ts t h t2 h2
  have h' := (List.pairwise_cons.mp h).1 t2
  apply h'
  trivial

private theorem insertTerm_head_grevlex (c : R) (m : Mon n) (ts : List (PolyTerm R n))
    (t : PolyTerm R n) (hgt : t.monomial.grevlex m = .gt)
    (hs : Sorted ts) (hs_hd : ∀ t' ∈ ts, t.monomial.grevlex t'.monomial = .gt) :
    ∀ r ∈ (insertTerm ⟨c,m⟩ ts), t.monomial.grevlex r.monomial = .gt := by
  induction ts with
  | nil =>
    simp only [insertTerm]
    intro r hr; simp at hr; subst hr; exact hgt
  | cons u rest ih =>
    have hu_gt := hs_hd u List.mem_cons_self
    have hrest_gt : ∀ t' ∈ rest, t.monomial.grevlex t'.monomial = .gt :=
      fun t' ht' => hs_hd t' (List.mem_cons_of_mem u ht')
    simp only [insertTerm]
    split
    · -- m.grevlex u.monomial = .gt
      intro r hr; simp at hr
      rcases hr with rfl | rfl | hr
      · exact hgt
      · exact hu_gt
      · exact hrest_gt r hr
    · -- m.grevlex u.monomial = .eq
      next heq =>
      have hm_eq : m = u.monomial := Mon.eq_of_grevlex.mp heq
      intro r hr; simp at hr
      rcases hr with rfl | hr
      · rw [hm_eq]; exact hu_gt
      · exact hrest_gt r hr
    · -- m.grevlex u.monomial = .lt
      intro r hr; simp at hr
      rcases hr with rfl | hr
      · exact hu_gt
      · exact ih (Sorted_tail hs) hrest_gt r hr

private theorem pairwise_cons_trans {R : α → α → Prop} [Trans R R R] {a b : α} {l : List α}
  : List.Pairwise R (a :: b :: l) ↔ R a b ∧ List.Pairwise R (b :: l) := by
  simp
  intro h1 h2 h3 a1 a1Hyp
  exact Trans.trans h3 (h1 a1 a1Hyp)

@[simp]
theorem sorted_cons {x : PolyTerm R n} :
    Sorted (x::xs) ↔ (∀ y ∈ xs, x.monomial.Grevlex y.monomial) ∧ Sorted xs := by
  simp [Sorted,List.pairwise_cons]

@[simp]
theorem sorted_nil : @Sorted n R [] := .nil

@[simp]
theorem sorted_singleton : Sorted [x] := by simp [Sorted]

@[simp high]
theorem sorted_cons_with_trans {x1 x2 : PolyTerm R n} {xs : List (PolyTerm R n) }:
    Sorted (x1::x2::xs) ↔ x1.monomial.Grevlex x2.monomial ∧ Sorted (x2 :: xs) := by
  simp
  intro sortedHyp1 sortedHyp2 x1x2Ord a amem
  specialize sortedHyp1 a amem
  exact Trans.trans x1x2Ord sortedHyp1

private theorem coalesceTerms_step_leadTerm (t : PolyTerm R n) (ts : List (PolyTerm R n)) :
    ∃ t' ts', coalesceTerms.step t ts = t'::ts' ∧ t'.monomial = t.monomial := by
  fun_induction coalesceTerms.step
  case case1 => simp
  case case2 ih =>
    simp at ih
    simp [ih]
  case case3 => simp

theorem coalesceTerms_sorted (terms : List (PolyTerm R n))
  (partiallySorted : List.Pairwise (fun a b => a.monomial.Grevlex b.monomial ∨ a.monomial = b.monomial) terms):
  Sorted (coalesceTerms terms) := by
  cases terms
  case nil => simp [coalesceTerms]
  case cons head tail =>
    simp [coalesceTerms]
    simp at partiallySorted
    induction tail generalizing head
    case nil => simp [coalesceTerms.step]
    case cons t ts ih =>
      unfold coalesceTerms.step
      split
      case isTrue monEq =>
        apply ih
        simp [monEq] at partiallySorted
        simp [partiallySorted, monEq]
        exact partiallySorted.left
      case isFalse monNeq =>
        let tsPartiallySorted := partiallySorted.right
        simp at tsPartiallySorted
        specialize ih t tsPartiallySorted
        let ⟨t',⟨ts',leadTermHyp'⟩⟩ := coalesceTerms_step_leadTerm t ts
        rw [leadTermHyp'.left] at ⊢ ih
        simp [ih, leadTermHyp'.right]
        let headOrdHyp := partiallySorted.left t (by simp)
        simp [monNeq] at headOrdHyp
        exact headOrdHyp

theorem sortTerms_sorted (terms : List (PolyTerm R n)) :
    Sorted (coalesceTerms (sortTerms terms)) := by
  apply coalesceTerms_sorted
  simp [sortTerms,Mon.grevlex_or_eq_iff_grevlex_ge]
  apply List.pairwise_mergeSort
  --prove the properties required for mergeSort
  case trans =>
    intro _ _ _
    simp [← Mon.grevlex_or_eq_iff_grevlex_ge]
    intro h1 h2
    cases h1
    case inl h1' =>
      cases h2
      case inl h2' =>
        simp [Trans.trans h1' h2']
      case inr h2' =>
        simp [h1',← h2']
    case inr h1' =>
      simp [h1', h2]
  case total =>
    have negTotal := @Std.Asymm.total_not (Mon n) Mon.Grevlex _
    intro a b
    generalize a.monomial = a
    generalize b.monomial = b
    have grevlexTric := @Std.Trichotomous.rel_or_eq_or_rel_swap (Mon n) Mon.Grevlex _ a b
    simp [← Mon.grevlex_or_eq_iff_grevlex_ge]
    rcases grevlexTric with h | h | h
    all_goals
      simp [h]

@[simp]
theorem insertTerms_mon_mem {x : PolyTerm R n} {xs : List (PolyTerm R n)} :
    t ∈ insertTerm x xs → (t.monomial = x.monomial) ∨ (∃ x ∈ xs, x.monomial = t.monomial) := by
  fun_induction insertTerm
  case case1 =>
    simp
    solve_by_elim
  case case2 =>
    simp
    intro h
    rcases h with h' | h' | h'
    case inl => simp [h']
    case inr.inl => simp [h']
    case inr.inr =>
      right; right
      exists t
  case case3 _ _ _ c =>
    simp
    intro h
    cases h with
    | inl h' =>
      simp [h']
    | inr h' =>
      right; right
      exists t
  case case4 ih =>
    simp
    intro h
    cases h with
    | inl h' =>
      simp [h']
    | inr h' =>
      specialize ih h'
      cases ih with
      | inl h'' => simp [h'']
      | inr h'' => simp [h'']

theorem sorted_insertTerm (t : PolyTerm R n) (ts : List (PolyTerm R n)) (hs : Sorted ts) :
    Sorted (insertTerm t ts) := by
  fun_induction insertTerm
  case case1 =>
    simp
  case case2 t ts ordHyp =>
    simp [← Mon.grevlex_iff_grevlex_gt] at ordHyp
    simp [ordHyp,hs]
  case case3 eqMonHyp coeff =>
    apply sorted_cons.mpr
    rewrite [sorted_cons] at hs
    simp at eqMonHyp
    simp [eqMonHyp]
    trivial
  case case4 t ts ordHyp ih =>
    simp [ih, Sorted_tail hs]
    intro y ymem
    simp [Mon.grevlex_flip, ← Mon.grevlex_iff_grevlex_gt] at ordHyp
    have ymem' := insertTerms_mon_mem ymem
    cases ymem' with
    | inl h => simp [h, ordHyp]
    | inr h =>
      have ⟨x,⟨xmem, xeq⟩⟩ := h
      simp [← xeq]
      simp at hs
      simp [hs, xmem]

theorem mergeTerms_mon_mem {xs ys : List (PolyTerm R n)} {m : Mon n} :
    (∃ t ∈ mergeTerms xs ys, t.monomial = m) ↔ (∃ x ∈ xs, x.monomial = m) ∨ (∃ y ∈ ys, y.monomial = m) := by
  sorry

@[simp]
theorem mergeTerms_nil_iff_nil (xs ys : List (PolyTerm R n)) :
  mergeTerms xs ys = [] ↔ xs = [] ∧ ys = [] := by
  constructor
  case mp =>
    intro mergeH
    cases xs with
    | nil => simp at mergeH; trivial
    | cons =>
      simp
      cases ys with
      | nil => simp at mergeH
      | cons =>
        simp [mergeTerms, mergeTerms.takeTillGE] at mergeH
        split at mergeH
        all_goals
          simp at mergeH
  case mpr =>
    simp
    intro hx hy
    simp [hx, hy]

@[simp]
theorem mergeTerms_cons_left {x : PolyTerm R n} {xs ys : List (PolyTerm R n)}
  (xsorted : Sorted (x :: xs)) (ysorted : Sorted ys)
  : mergeTerms (x :: xs) ys = insertTerm x (mergeTerms xs ys) := by
  induction xs
  case nil =>
    simp
  case cons xhead xtail ih1 =>
    induction ys
    case nil =>
      simp at xsorted
      simp [xsorted]
    case cons ih2 =>
      conv =>
        left
        unfold mergeTerms mergeTerms.takeTillGE
      split
      case h_1 ordH =>
        sorry
      case h_2 eqH =>
        sorry
      case h_3 ordH =>
        conv at ih1 =>
          right
          left
          unfold mergeTerms
        have xConsTailSorted : Sorted (x :: xtail) := by
          sorry
        simp [xConsTailSorted, Sorted_tail ysorted] at ih1 ih2

        sorry

@[simp]
theorem mulTerms_nil_left (ys : List (PolyTerm R n)) : mulTerms [] ys = [] := by
  simp [mulTerms]

@[simp]
theorem mulTerms_nil_right (xs : List (PolyTerm R n)) : mulTerms xs [] = [] := by
  unfold mulTerms
  simp
  split
  all_goals trivial

@[simp]
theorem mulTerms_cons_left (x : PolyTerm R n) (xs ys : List (PolyTerm R n))
  (xsorted : Sorted (x :: xs)) (ysorted : Sorted ys)
  : mulTerms (x :: xs) ys = mergeTerms (mulMonTerms x.coefficient x.monomial ys) (mulTerms xs ys) := by
  sorry

@[simp]
theorem mulTerms_cons_right (y : PolyTerm R n) (xs ys : List (PolyTerm R n))
  (xsorted : Sorted xs) (ysorted : Sorted (y :: ys))
  : mulTerms xs (y :: ys) = mergeTerms (mulMonTerms y.coefficient y.monomial xs) (mulTerms xs ys) := by sorry

theorem sorted_mergeTerms (xs ys : List (PolyTerm R n)) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mergeTerms xs ys) := by
  induction xs generalizing ys
  case nil => simpa
  case cons ih1 =>
    simp [mergeTerms_cons_left hx hy] --why isn't mergeTerms_cons_left triggering directly despite being a simp theorem?
    apply sorted_insertTerm
    apply ih1
    apply Sorted_tail hx
    apply hy

theorem sorted_mulMonTerms (xs : List (PolyTerm R n)) (hx : Sorted xs) :
    Sorted (mulMonTerms c m xs) := by
  simp [Sorted,mulMonTerms, List.pairwise_map, ← Mon.grevlex_mul_mono]
  exact hx

theorem sorted_mulTerms (xs ys : List (PolyTerm R n)) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mulTerms xs ys) := by
  fun_induction mulTerms
  case case1 => trivial
  case case2 => simp [Sorted]
  case case3 ysh ih =>
    simp [ysh, Sorted_tail hx] at ih
    simp at hx
    simp [hx]
    constructor
    case left =>
      intro y ymem
      sorry
    case right =>
      apply sorted_mergeTerms
      case hx =>
        apply sorted_mulMonTerms
        simp [ysh] at hy
        simp [hy]
      case hy => trivial

theorem sorted_removeZeros [BEq R] (terms : List (PolyTerm R n)) : Sorted terms → Sorted (removeZeros terms) := by
  unfold removeZeros
  intro h
  fun_induction List.filter
  case case1 => trivial
  case case2 coeffh ih =>
    rw [sorted_cons] at h
    apply sorted_cons.mpr
    simp at coeffh
    simp [h.2] at ih
    simp [ih]
    intros
    apply h.1
    trivial
  case case3 coeffh ih =>
    rw [sorted_cons] at h
    simp [ih, h]

theorem sorted_add [BEq R] (p q : Polynomial R n) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (add p q).terms := sorted_removeZeros _ <| sorted_mergeTerms p.terms q.terms hp hq

theorem sorted_mul [BEq R] (p q : Polynomial R n) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (mul p q).terms := sorted_removeZeros _ <| sorted_mulTerms p.terms q.terms hp hq

/-! ## Denotation theorems -/

private theorem zero_add' (a : R) : 0 + a = a := by rw [add_comm, add_zero]

private theorem add_left_comm' (a b c : R) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

private theorem add_cancel (a b c d : R) (h : a + c = 0) :
    (a + b) + (c + d) = b + d := by
  rw [add_assoc, add_left_comm' b c d, ← add_assoc, h, zero_add']

theorem denote_mk (ctx : Context R) (ts : List (PolyTerm R n)) :
    denote ctx ⟨ts⟩ = denoteTerms ctx ts := rfl

@[simp] theorem denoteTerms_nil (ctx : Context R) :
    denoteTerms ctx ([] : List (PolyTerm R n)) = 0 := rfl

@[simp] theorem denoteTerms_cons (ctx : Context R) (t : PolyTerm R n) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (t :: ts) = t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts := rfl

theorem denote_zero (ctx : Context R) : denote ctx (zero : Polynomial R n) = 0 := rfl

theorem denote_cons_eq (ctx : Context R) (t : PolyTerm R n) (ts : List (PolyTerm R n)) :
    denote ctx ⟨t :: ts⟩ = t.coefficient * t.monomial.denote ctx + denote ctx ⟨ts⟩ := rfl

@[simp] theorem denoteTerms_append (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (xs ++ ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  induction xs with
  | nil => exact (zero_add' _).symm
  | cons x xs ih => simp [ih, add_assoc]

theorem denote_leadTerm_tail (ctx : Context R) (p : Polynomial R n)
    (t : PolyTerm R n) (ts : List (PolyTerm R n)) (h : p.terms = t :: ts) :
    denote ctx p = t.coefficient * t.monomial.denote ctx + denote ctx p.tail := by
  simp [denote, tail, h]

theorem denoteTerms_insertTerm (ctx : Context R) (t : PolyTerm R n) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (insertTerm t ts) = t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts := by
  induction ts with
  | nil => simp only [insertTerm];
           simp [add_zero]
  | cons t' rest ih =>
    simp only [insertTerm]; split
    next h =>
      simp
    · next hg => have hm : t.monomial = t'.monomial := by
                    apply Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex)
                    trivial
                 simp
                 grind
    · simp only [denoteTerms_cons]; rw [ih, add_left_comm']

-- Add instances to let ac_nf work
instance : Std.Associative (α := R) (.*.) := ⟨mul_assoc⟩
instance : Std.Commutative (α := R) (.*.) := ⟨CommRing.mul_comm⟩

instance : Std.Associative (α := R) (.+.) := ⟨add_assoc⟩
instance : Std.Commutative (α := R) (.+.) := ⟨add_comm⟩

variable [beq : BEq R] [lawfulbeq : LawfulBEq R]

theorem denoteTerms_removeZeros (ctx : Context R) (terms : List (PolyTerm R n)) :
  denoteTerms ctx (removeZeros terms) = denoteTerms ctx terms := by
  unfold removeZeros
  fun_induction List.filter
  case case1 => trivial
  case case2 ih =>
    simp [ih]
  case case3 coeffh ih =>
    simp at coeffh
    simp [ih, coeffh, Semiring.zero_mul, zero_add']

omit beq lawfulbeq in
theorem denoteTerms_mergeTerms (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (mergeTerms xs ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  induction xs generalizing ys
  case nil => simp [zero_add']
  case cons head tail ih1 =>
    simp
    unfold mergeTerms
    induction ys
    case nil =>
      simp [Semiring.add_zero, mergeTerms.takeTillGE]
    case cons ih2 =>
      unfold mergeTerms.takeTillGE
      split
      case h_1 =>
        simp [ih1]
        ac_nf
      case h_2 monEqH =>
        simp at monEqH
        simp [ih1, monEqH, Semiring.right_distrib]
        ac_nf
      case h_3 =>
        simp [ih2]
        ac_nf

theorem denote_add (ctx : Context R) (p q : Polynomial R n) :
    denote ctx (add p q) = denote ctx p + denote ctx q := by
  unfold Polynomial.add denote
  simp [denoteTerms_removeZeros, denoteTerms_mergeTerms]

omit beq lawfulbeq in
theorem denoteTerms_map_smul (ctx : Context R) (c : R) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, t.monomial⟩) = c * denoteTerms ctx ts := by
  induction ts with
  | nil => simp [mul_zero]
  | cons t ts ih => simp [ih, left_distrib, mul_assoc]

omit beq lawfulbeq in
theorem denote_smul (ctx : Context R) (c : R) (p : Polynomial R n) :
    denote ctx (smul c p) = c * denote ctx p := by simp [smul, denote, denoteTerms_map_smul]

omit beq lawfulbeq in
theorem denoteTerms_map_mulMon (ctx : Context R) (c : R) (m : Mon n) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, m.mul t.monomial⟩) =
    c * m.denote ctx * denoteTerms ctx ts := by
  induction ts with
  | nil => simp [mul_zero]
  | cons t ts ih =>
    simp only [List.map_cons, denoteTerms_cons, ih]
    rw [left_distrib, mul_assoc, mul_assoc]; congr 1
    ac_nf
    congr
    apply Macaulean.Mon.denote_mul

omit beq lawfulbeq in
theorem denoteTerms_mulMonTerms (ctx : Context R) (c : R) (m : Mon n) (p : List (PolyTerm R n)) :
    denoteTerms ctx (mulMonTerms c m p) = c * m.denote ctx * denoteTerms ctx p := by
  simp [mulMonTerms, denoteTerms_map_mulMon]

omit beq lawfulbeq in
theorem denoteTerms_mulTerms (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (mulTerms xs ys) = denoteTerms ctx xs * denoteTerms ctx ys := by
  fun_induction mulTerms
  case case1 => simp [Semiring.zero_mul]
  case case2 ysEmpty => simp [ysEmpty,denoteTerms_nil,Semiring.mul_zero]
  case case3 xs' _ _ ys' ysCons ih =>
    simp [denoteTerms_mergeTerms, denoteTerms_mulMonTerms, Mon.denote_mul]
    simp [ih,← ysCons,Semiring.right_distrib]
    simp [ysCons,Semiring.left_distrib]
    ac_nf

theorem denote_mul (ctx : Context R) (p q : Polynomial R n) :
    denote ctx (mul p q) = denote ctx p * denote ctx q := by
    unfold denote Polynomial.mul
    simp [denoteTerms_mulTerms, denoteTerms_removeZeros]

omit beq lawfulbeq in
theorem denote_singleton (ctx : Context R) (i : Fin n)
  : denote ctx (ofTerm ⟨c, Mon.fromVar (n := n) i⟩) = c * (ctx.get i):= by
  simp [denote, ofTerm]
  conv =>
    lhs
    left
    right
    apply Mon.denote_fromVar ctx (Mon.fromVar i)
  simp [getElem, Semiring.add_zero]

omit beq lawfulbeq in
theorem denote_singleton_no_constant (ctx : Context R) (x : R) (i : Fin n) (h2 : ctx.get i = x) : denote ctx (ofVar i) = x := by
  simp [denote, ofVar, ofTerm]
  conv =>
    lhs
    left
    right
    apply Mon.denote_fromVar ctx (Mon.fromVar i)
  simp [getElem, Semiring.add_zero, h2, Semiring.one_mul]

omit beq lawfulbeq in
theorem denote_plus_const (ctx : Context R) (c : R) (p : Polynomial R n) :
  denote ctx (addTerm ⟨c, Mon.unit⟩ p) = denote ctx p + c := by
  simp [addTerm,denote,denoteTerms_insertTerm,Mon.denote_unit,Semiring.mul_one]
  ac_nf

omit beq lawfulbeq in
theorem denote_const (ctx : Context R) (c : R) :
  denote (n := n) ctx ⟨[⟨c,Mon.unit⟩]⟩ = c := by
  simp [denote, denoteTerms, Mon.denote_unit]
  grind

omit beq lawfulbeq in
@[simp] theorem denoteTerms_empty (ctx : Context R) :
  denoteTerms ctx ([] : List (PolyTerm R n)) = 0 := rfl

omit beq lawfulbeq in
theorem denote_neg (ctx : Context R) (p : Polynomial R n) :
    denote ctx (-p) = -denote ctx p := by
  have ⟨terms⟩ := p
  simp [denote, Neg.neg, Polynomial.neg]
  induction terms
  case nil => simp; grind
  case cons t ts indHyp =>
    simp [indHyp]
    grind

omit beq lawfulbeq in
private theorem foil (a b c d : R) :
    (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [right_distrib, left_distrib, left_distrib]; simp only [add_assoc]

theorem mul_leadTerm_expand (ctx : Context R)
    (tf : PolyTerm R n) (f' : List (PolyTerm R n))
    (tg : PolyTerm R n) (g' : List (PolyTerm R n)) :
    denote ctx (mul ⟨tf :: f'⟩ ⟨tg :: g'⟩) =
      tf.coefficient * tg.coefficient * (tf.monomial.mul tg.monomial).denote ctx
      + tf.coefficient * tf.monomial.denote ctx * denoteTerms ctx g'
      + denoteTerms ctx f' * tg.coefficient * tg.monomial.denote ctx
      + denoteTerms ctx f' * denoteTerms ctx g' := by
  rw [denote_mul]; simp only [denote_mk, denoteTerms_cons]; rw [foil]
  ac_nf
  simp [Mon.denote_mul]

end Theorems
end Polynomial

end Macaulean
