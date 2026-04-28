import Macaulean.Polynomial.Basic
import Lean
open Lean Grind CommRing

namespace Macaulean

namespace Mon


/-! ## Lemmas about grevlex -/
@[simp]
theorem eq_of_grevlex {m1 m2 : Mon n} : (h : m1.grevlex m2 = .eq) → m1 = m2 :=
  Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex)

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
      exact Trans.trans heq.2 heq2.2

theorem grevlex_swap (m₁ m₂ : Mon n) :
    (Mon.grevlex m₁ m₂).swap = Mon.grevlex m₂ m₁ :=
    Eq.symm (inferInstance : Std.OrientedCmp (grevlex (n := n))).1

theorem grevlex_flip {m₁ m₂ : Mon n} (h : m₁.grevlex m₂ = .lt) :
    m₂.grevlex m₁ = .gt := by
  have := grevlex_swap m₁ m₂; rw [h] at this; simpa using this.symm

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

/-- Monotonicity of grevlex under monomial multiplication -- requires structural induction. -/
private theorem grevlex_mul_mono {m₁ m₂ m : Mon n}
    (h : m₁.grevlex m₂ = .gt) : (m.mul m₁).grevlex (m.mul m₂) = .gt := by
  simp [Mon.grevlex, degree_mul, Ordering.then_eq_gt] at *
  cases h
  case inl hdeg =>
    replace hdeg := Nat.compare_eq_gt.mp hdeg
    simp [Nat.compare_eq_gt]
    left
    trivial
  case inr hNext =>
    right
    have ⟨hdeg, hlex⟩ := hNext
    refine ⟨ hdeg, ?_⟩
    apply List.lt_iff_exists.mpr
    replace hlex := List.lt_iff_exists.mp hlex
    --find the i where the powers differ
    rcases hlex with ⟨i, ltn⟩
    sorry
    sorry


/-! ## Denotational Lemmas for monomials -/
theorem degree_unit_iff (m : Mon n) : m.degree = 0 ↔ m = unit := by
  constructor
  case mp =>
    intro
    sorry
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

@[simp]
theorem mergeTerms_nil_left [CommRing R] [BEq R] (xs : List (PolyTerm R n)) : mergeTerms [] xs = xs := by simp

@[simp]
theorem mergeTerms_nil_right [CommRing R] [BEq R] (xs : List (PolyTerm R n)) : mergeTerms xs [] = xs := by
  unfold mergeTerms
  split
  all_goals trivial

/-! ## Denotation theorems -/

section Theorems
variable {R : Type} [inst : Grind.CommRing R] [deceq : DecidableEq R] [lawfuleq : LawfulBEq R]
open Grind.Semiring Grind.Ring Grind.CommSemiring
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast

omit deceq in
private theorem zero_add' (a : R) : 0 + a = a := by rw [add_comm, add_zero]

omit deceq in
private theorem add_left_comm' (a b c : R) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

omit deceq in
private theorem add_cancel (a b c d : R) (h : a + c = 0) :
    (a + b) + (c + d) = b + d := by
  rw [add_assoc, add_left_comm' b c d, ← add_assoc, h, zero_add']

omit deceq in
theorem denote_mk (ctx : Context R) (ts : List (PolyTerm R n)) :
    denote ctx ⟨ts⟩ = denoteTerms ctx ts := rfl

omit deceq in
@[simp] theorem denoteTerms_nil (ctx : Context R) :
    denoteTerms ctx ([] : List (PolyTerm R n)) = 0 := rfl

omit deceq in
@[simp] theorem denoteTerms_cons (ctx : Context R) (t : PolyTerm R n) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (t :: ts) = t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts := rfl

omit deceq in
theorem denote_zero (ctx : Context R) : denote ctx (zero : Polynomial R n) = 0 := rfl

omit deceq in
theorem denote_cons_eq (ctx : Context R) (t : PolyTerm R n) (ts : List (PolyTerm R n)) :
    denote ctx ⟨t :: ts⟩ = t.coefficient * t.monomial.denote ctx + denote ctx ⟨ts⟩ := rfl

omit deceq in
@[simp] theorem denoteTerms_append (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (xs ++ ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  induction xs with
  | nil => exact (zero_add' _).symm
  | cons x xs ih => simp [ih, add_assoc]

omit deceq in
theorem denote_leadTerm_tail (ctx : Context R) (p : Polynomial R n)
    (t : PolyTerm R n) (ts : List (PolyTerm R n)) (h : p.terms = t :: ts) :
    denote ctx p = t.coefficient * t.monomial.denote ctx + denote ctx p.tail := by
  simp [denote, tail, h]

theorem denoteTerms_insertTerm (ctx : Context R) (c : R) (m : Mon n) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (insertTerm c m ts) = c * m.denote ctx + denoteTerms ctx ts := by
  induction ts with
  | nil => simp only [insertTerm];
           simp [add_zero]
  | cons t rest ih =>
    simp only [insertTerm]; split
    next h =>
      simp
    · next hg => have hm : m = t.monomial := by
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

theorem denoteTerms_mergeTerms (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (mergeTerms xs ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  sorry

theorem denote_add (ctx : Context R) (p q : Polynomial R n) :
    denote ctx (add p q) = denote ctx p + denote ctx q := by
  unfold Polynomial.add denote
  simp [denoteTerms_removeZeros, denoteTerms_mergeTerms]

omit deceq in
theorem denoteTerms_map_smul (ctx : Context R) (c : R) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, t.monomial⟩) = c * denoteTerms ctx ts := by
  induction ts with
  | nil => simp [mul_zero]
  | cons t ts ih => simp [ih, left_distrib, mul_assoc]

omit deceq in
theorem denote_smul (ctx : Context R) (c : R) (p : Polynomial R n) :
    denote ctx (smul c p) = c * denote ctx p := by simp [smul, denote, denoteTerms_map_smul]

omit deceq in
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

omit deceq in
theorem denote_mulMonTerms (ctx : Context R) (c : R) (m : Mon n) (p : List (PolyTerm R n)) :
    denoteTerms ctx (mulMonTerms c m p) = c * m.denote ctx * denoteTerms ctx p := by
  simp [mulMonTerms, denoteTerms_map_mulMon]

theorem denote_mulTerms (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (mulTerms xs ys) = denoteTerms ctx xs * denoteTerms ctx ys := by
  induction xs with
  | nil => simp [mulTerms, zero_mul]
  | cons t ts ih =>
    sorry


theorem denote_mul (ctx : Context R) (p q : Polynomial R n) :
    denote ctx (mul p q) = denote ctx p * denote ctx q := by
    unfold denote Polynomial.mul
    simp [denote_mulTerms, denoteTerms_removeZeros]

omit deceq in
theorem denote_singleton (ctx : Context R) (i : Fin n)
  : denote ctx (ofTerm ⟨c, Mon.fromVar (n := n) i⟩) = c * (ctx.get i):= by
  simp [denote, ofTerm]
  conv =>
    lhs
    left
    right
    apply Mon.denote_fromVar ctx (Mon.fromVar i)
  simp [getElem, Semiring.add_zero]

omit deceq in
theorem denote_singleton_no_constant (ctx : Context R) (x : R) (i : Fin n) (h2 : ctx.get i = x) : denote ctx (ofVar i) = x := by
  simp [denote, ofVar, ofTerm]
  conv =>
    lhs
    left
    right
    apply Mon.denote_fromVar ctx (Mon.fromVar i)
  simp [getElem, Semiring.add_zero, h2, Semiring.one_mul]

theorem denote_plus_const (ctx : Context R) (c : R) (p : Polynomial R n) :
  denote ctx (addTerm p c Mon.unit) = denote ctx p + c := by
  sorry

omit deceq in
theorem denote_const (ctx : Context R) (c : R) :
  denote (n := n) ctx ⟨[⟨c,Mon.unit⟩]⟩ = c := by
  simp [denote, denoteTerms, Mon.denote_unit]
  grind



omit deceq in
@[simp] theorem denoteTerms_empty (ctx : Context R) :
  denoteTerms ctx ([] : List (PolyTerm R n)) = 0 := rfl

omit deceq in
theorem denote_neg (ctx : Context R) (p : Polynomial R n) :
    denote ctx (-p) = -denote ctx p := by
  have ⟨terms⟩ := p
  simp [denote, Neg.neg, Polynomial.neg]
  induction terms
  case nil => simp; grind
  case cons t ts indHyp =>
    simp [indHyp]
    grind

omit deceq in
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

/-! ## Sortedness preservation -/

omit inst deceq in
private theorem Sorted_tail {t : PolyTerm R n} {ts : List (PolyTerm R n)}
    (h : Sorted (t :: ts)) : Sorted ts := (List.pairwise_cons.mp h).2

omit inst deceq in
private theorem Sorted_head_gt_all :
    ∀ (ts : List (PolyTerm R n)) (t : PolyTerm R n),
    Sorted (t :: ts) → ∀ t' ∈ ts, t.monomial.grevlex t'.monomial = .gt := by
  intro ts t h t2 h2
  have h' := (List.pairwise_cons.mp h).1 t2
  apply h'
  trivial

private theorem insertTerm_head_grevlex (c : R) (m : Mon n) (ts : List (PolyTerm R n))
    (t : PolyTerm R n) (hgt : t.monomial.grevlex m = .gt)
    (hs : Sorted ts) (hs_hd : ∀ t' ∈ ts, t.monomial.grevlex t'.monomial = .gt) :
    ∀ r ∈ (insertTerm c m ts), t.monomial.grevlex r.monomial = .gt := by
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
      have hm_eq : m = u.monomial := Mon.eq_of_grevlex heq
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


theorem sorted_insertTerm (c : R) (m : Mon n) (ts : List (PolyTerm R n)) (hs : Sorted ts) :
    Sorted (insertTerm c m ts) := by
  induction ts with
  | nil =>
    simp only [insertTerm]
    unfold Sorted
    simp
  | cons t rest ih =>
    have hs_rest := Sorted_tail hs
    simp only [insertTerm]
    let rel : PolyTerm R n → PolyTerm R n → Prop :=
      fun t₁ t₂ => t₁.monomial.grevlex t₂.monomial = .gt
    have trans : Trans rel rel rel := ⟨Mon.grevlex_trans⟩
    split
    · -- m.grevlex t.monomial = .gt
      next hgt =>
        apply pairwise_cons_trans.mpr
        exact ⟨hgt, hs⟩
    · -- m.grevlex t.monomial = .eq
      next heq =>
      have hm_eq : m = t.monomial := Mon.eq_of_grevlex heq
      subst hm_eq
      clear heq
      cases rest with
      | nil => apply List.pairwise_singleton
      | cons t' rest' =>
          apply pairwise_cons_trans.mpr
          constructor
          · exact (pairwise_cons_trans.mp hs).1
          · exact hs_rest
    · -- m.grevlex t.monomial = .lt
      next hlt =>
      have hgt := Mon.grevlex_flip hlt
      have ih_result := ih hs_rest

      cases h : insertTerm c m rest with
      | nil => apply List.pairwise_singleton
      | cons r rest' =>
        rw [h] at ih_result
        apply pairwise_cons_trans.mpr
        apply And.intro ?_ ih_result
        have rContHyp : r ∈ insertTerm c m rest := by simp [h]
        apply insertTerm_head_grevlex _ _ _ _ hgt hs_rest _ r rContHyp
        intro t'
        exact List.rel_of_pairwise_cons hs

theorem mergeTerms_monomials {xs ys : List (PolyTerm R n)}
  : (mergeTerms xs ys).map (PolyTerm.monomial) ⊆ (xs.map PolyTerm.monomial) ++ (ys.map PolyTerm.monomial) := by
  sorry

theorem sorted_mergeTerms (xs ys : List (PolyTerm R n)) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mergeTerms xs ys) := by
  -- stop
  induction xs generalizing ys
  case nil => trivial
  case cons =>
    unfold mergeTerms
    split
    case h_1 => trivial
    case h_2 => trivial
    case h_3 ih _ _ _ x xs' heq ysNonEmpty =>
      injection heq with heq1 heq2
      rw [heq2] at ih
      unfold Sorted at hx
      simp [heq1, heq2] at hx
      let ⟨hx1, hx2⟩ := hx
      simp [hx2] at ih
      fun_induction mergeTerms.takeTillGE
      case case1 => trivial
      case case2 =>
        unfold Sorted
        refine List.pairwise_cons.mpr ?_
        and_intros
        case refine_1 => sorry
        case refine_2 =>
          apply ih
          apply hy
      case case3 x c =>
        simp
        and_intros
        case refine_1 => sorry
        case refine_2 =>
          apply ih
          simp at hy
          apply hy.2
      case case4 ih1 =>
        simp
        and_intros
        case refine_1 => sorry
        case refine_2 ts x =>
          by_cases h : ts = []
          case pos =>
            simp [h]
            trivial
          case neg =>
            apply ih1 h _
            simp at hy
            apply hy.2


theorem sorted_removeZeros (terms : List (PolyTerm R n)) : Sorted terms → Sorted (removeZeros terms) := by
  unfold removeZeros
  intro h
  fun_induction List.filter
  case case1 => trivial
  all_goals
    simp [List.pairwise_cons] at h
  case case2 coeffh ih =>
    simp at coeffh
    simp [ih, h]
    intros
    apply h.1
    trivial
  case case3 coeffh ih =>
    simp [ih, h]

theorem sorted_add (p q : Polynomial R n) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (add p q).terms := sorted_removeZeros _ <| sorted_mergeTerms p.terms q.terms hp hq

theorem sorted_mul (p q : Polynomial R n) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (mul p q).terms := by
  sorry

end Theorems
end Polynomial

end Macaulean
