import Macaulean.Polynomial.Basic
import Lean
open Lean Grind CommRing Meta

namespace Macaulean

namespace Mon

/-! ## Lemmas about grevlex

`grevlex` is now a single `compare` of the packed keys, so the order-theoretic
facts are exactly the ones for `Nat`.  That the resulting order really is
grevlex is `Mon.grevlex_eq_grevlexSpec`.
-/
@[simp]
theorem eq_of_grevlex {m1 m2 : Mon n} : (m1.grevlex m2 = .eq) ↔ m1 = m2 := by
  constructor
  case mp =>
    exact Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex)
  case mpr =>
    rintro rfl; simp [grevlex_eq_compare]

@[simp]
theorem grevlex_rfl {m : Mon n} : m.grevlex m = .eq :=
  by simp

theorem grevlex_trans {m1 m2 m3 : Mon n} (h1 : m1.grevlex m2 = .gt) (h2 : m2.grevlex m3 = .gt) :
    m1.grevlex m3 = .gt := by
  rw [grevlex_eq_compare, Nat.compare_eq_gt] at *
  omega

theorem grevlex_swap (m₁ m₂ : Mon n) :
    (Mon.grevlex m₁ m₂).swap = Mon.grevlex m₂ m₁ :=
    Eq.symm (inferInstance : Std.OrientedCmp (grevlex (n := n))).1

theorem grevlex_flip {m₁ m₂ : Mon n} :
  m₁.grevlex m₂ = .lt ↔ m₂.grevlex m₁ = .gt := by
  rw [grevlex_eq_compare, grevlex_eq_compare, Nat.compare_eq_lt, Nat.compare_eq_gt]

/-- Monotonicity of grevlex under monomial multiplication: multiplication is
addition of keys, so this is monotonicity of `Nat.add`. -/
theorem grevlex_mul_mono_left {m₁ m₂ m : Mon n}
    : m₁.Grevlex m₂ ↔ (m.mul m₁).Grevlex (m.mul m₂) := by
  simp only [Grevlex, mul_key]
  omega

instance : @Std.Commutative (Mon n) Mon.mul where
  comm a b := by
    have h : a.key + b.key = b.key + a.key := Nat.add_comm _ _
    simp only [mul, h]

theorem grevlex_mul_mono_right {m₁ m₂ m : Mon n}
    : m₁.Grevlex m₂ ↔ (m₁.mul m).Grevlex (m₂.mul m) := by
  simp only [Grevlex, mul_key]
  omega

/-! ## Exponent vectors of packed monomials -/

theorem sum_zipWith_add : ∀ (p q : List Nat), p.length = q.length →
    (List.zipWith (· + ·) p q).sum = p.sum + q.sum := by
  intro p
  induction p with
  | nil => intro q hq; cases q <;> simp_all
  | cons e es ih =>
    intro q hq
    cases q with
    | nil => simp at hq
    | cons f fs =>
      have := ih fs (by simpa using hq)
      simp only [List.zipWith_cons_cons, List.sum_cons, this]
      omega

/-- The exponent vector of a product is the sum of the exponent vectors, as
long as the degrees still fit in one digit. -/
theorem powers_mul {m1 m2 : Mon n} (h1 : m1.WF) (h2 : m2.WF)
    (hlt : m1.degree + m2.degree < base n) :
    (m1.mul m2).powers = List.zipWith (· + ·) m1.powers m2.powers := by
  have hkey : (m1.mul m2).key
      = encodeKey (base n) (List.zipWith (· + ·) m1.powers m2.powers) := by
    rw [mul_key, h1.2, h2.2]
    exact encodeKey_add _ _ _ (by simp)
  show decodeKey (base n) n (m1.mul m2).key = _
  rw [hkey]
  refine decodeKey_encodeKey _ (base_pos n) _ n (by simp) ?_
  rw [sum_zipWith_add _ _ (by simp)]
  exact hlt

theorem degree_mul {m1 m2 : Mon n} (h1 : m1.WF) (h2 : m2.WF)
    (hlt : m1.degree + m2.degree < base n) :
    (m1.mul m2).degree = m1.degree + m2.degree := by
  rw [degree, powers_mul h1 h2 hlt, sum_zipWith_add _ _ (by simp)]
  rfl

theorem wf_mul {m1 m2 : Mon n} (h1 : m1.WF) (h2 : m2.WF)
    (hlt : m1.degree + m2.degree < base n) : (m1.mul m2).WF := by
  refine ⟨?_, ?_⟩
  · rw [← degree]; rw [degree_mul h1 h2 hlt]; exact hlt
  · rw [powers_mul h1 h2 hlt, mul_key, h1.2, h2.2, encodeKey_add _ _ _ (by simp)]

/-! ## Denotational Lemmas for monomials -/
theorem degree_unit_iff (m : Mon n) (h : m.WF) : m.degree = 0 ↔ m = unit := by
  constructor
  case mp =>
    intro hd
    rw [degree, List.sum_eq_zero_iff_forall_eq_nat] at hd
    have hz : m.powers = List.replicate n 0 := by
      have := List.eq_replicate_of_mem hd
      rwa [m.powers_length] at this
    rw [← key_eq_iff_eq, h.2, hz, encodeKey_replicate_zero, unit_key]
  case mpr =>
    rintro rfl
    simp [degree, powers_unit]

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
  rw [powers_unit]
  induction n
  case zero => trivial
  case succ ih => simp [List.replicate_succ', Semiring.pow_zero, ih]

/-! ### One-hot exponent vectors -/

private theorem sum_ofFn_zero (m : Nat) : (List.ofFn (fun _ : Fin m => (0:Nat))).sum = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.ofFn_succ]; simpa using ih

theorem sum_ofFn_oneHot : ∀ (m : Nat) (i : Fin m) (k : Nat),
    (List.ofFn (fun j : Fin m => if j == i then k else 0)).sum = k := by
  intro m
  induction m with
  | zero => intro i; exact absurd i.isLt (by omega)
  | succ m ih =>
    intro i k
    rw [List.ofFn_succ, List.sum_cons]
    rcases i with ⟨iv, hiv⟩
    cases iv with
    | zero =>
      have hf : (fun (j : Fin m) => if j.succ == (⟨0, hiv⟩ : Fin (m+1)) then k else 0)
          = (fun _ : Fin m => (0:Nat)) := by
        funext j
        have hb : (j.succ == (⟨0, hiv⟩ : Fin (m+1))) = false := by
          simp [Fin.ext_iff, Fin.val_succ]
        rw [hb]
        rfl
      have h0 : ((0 : Fin (m+1)) == (⟨0, hiv⟩ : Fin (m+1))) = true := by
        simp
      rw [hf, sum_ofFn_zero, h0]
      show k + 0 = k
      omega
    | succ iv =>
      have hlt : iv < m := by omega
      have h0 : ((0 : Fin (m+1)) == (⟨iv+1, hiv⟩ : Fin (m+1))) = false := by
        simp [Fin.ext_iff]
      have hf : (fun (j : Fin m) => if j.succ == (⟨iv+1, hiv⟩ : Fin (m+1)) then k else 0)
          = (fun j : Fin m => if j == (⟨iv, hlt⟩ : Fin m) then k else 0) := by
        funext j
        by_cases hj : j.val = iv
        · have e1 : j.succ = (⟨iv+1, hiv⟩ : Fin (m+1)) := by
            apply Fin.ext; simp [Fin.val_succ, hj]
          have e2 : j = (⟨iv, hlt⟩ : Fin m) := by apply Fin.ext; simp [hj]
          rw [if_pos (by simpa using e1), if_pos (by simpa using e2)]
        · have e1 : ¬ (j.succ = (⟨iv+1, hiv⟩ : Fin (m+1))) := by
            intro he
            exact hj (by have := congrArg Fin.val he; simp [Fin.val_succ] at this; omega)
          have e2 : ¬ (j = (⟨iv, hlt⟩ : Fin m)) := fun he => hj (by rw [he])
          rw [if_neg (by simpa using e1), if_neg (by simpa using e2)]
      rw [h0, hf, ih ⟨iv, hlt⟩ k]
      show (0:Nat) + k = k
      omega

theorem powers_fromVarPower (i : Fin n) (k : Nat) (hk : k < base n) :
    (fromVarPower i k).powers = List.ofFn (fun j => if j == i then k else 0) :=
  powers_ofPowersN (by simp) (by rw [sum_ofFn_oneHot]; exact hk)

set_option backward.isDefEq.respectTransparency false in
theorem denote_fromVarPower (ctx : Context R) (i : Fin n) (k : Nat) (hk : k < base n)
  : denote ctx (.fromVarPower i k) = (ctx[i])^k := by
  rw [denote, powers_fromVarPower i k hk]
  clear hk
  rw [List.mapFinIdx_eq_ofFn]
  simp [List.ofFn, Fin.foldr_eq_finRange_foldr, List.foldl_map]
  induction n
  case zero =>
    have h := i.isLt
    contradiction
  case succ m ih1 =>
    have h := i.isLt
    by_cases ivalH : Fin.last m = i
    case pos =>
      simp [← ivalH, List.finRange_succ_last, List.foldl_map, GetElem.getElem]
      have succ_neq_last := fun y => Fin.ne_of_lt (Fin.castSucc_lt_last (n:=m) y)
      simp [succ_neq_last, Semiring.pow_zero, Semiring.mul_one]
      clear ivalH i h ih1 succ_neq_last
      generalize (RArray.get ctx m) = t
      induction m
      case zero => simp [Semiring.one_mul]
      case succ m' ih2 =>
        simp [List.foldl_cons, List.finRange_succ, List.foldl_map, ih2]
    case neg =>
      specialize ih1 (Fin.castLT i (by grind))
      conv at ih1 =>
        enter [1, 1, _, _, 2, 2, 1]
        rw [← Fin.castSucc_inj]
      simp [Fin.castSucc_castLT] at ih1
      simp [List.finRange_succ_last, List.foldl_map, GetElem.getElem, ivalH,
        Semiring.pow_zero, Semiring.mul_one]
      exact ih1

theorem denote_fromVar (ctx : Context R) (i : Fin n)
  : denote ctx (.fromVar i) = ctx[i] := by
  unfold fromVar
  rw [denote_fromVarPower _ _ _ (one_lt_base n)]
  simp [Semiring.pow_one]

private theorem denote_zipWith (ctx : Context R) : ∀ (m : Nat) (p q : List Nat),
    p.length = m → q.length = m →
      ((List.zipWith (· + ·) p q).mapFinIdx (fun i k _ => (ctx.get i ^ k))).foldl (.*.) 1
        = (((p.mapFinIdx (fun i k _ => (ctx.get i ^ k))).foldl (.*.) 1)
            * ((q.mapFinIdx (fun i k _ => (ctx.get i ^ k))).foldl (.*.) 1)) := by
  intro m
  induction m with
  | zero =>
    intro p q hp hq
    simp only [List.length_eq_zero_iff] at hp hq
    subst hp; subst hq
    show (1:R) = 1 * 1
    rw [Semiring.one_mul]
  | succ m ih =>
    intro m1powers m2powers m1length m2length
    specialize ih m1powers.dropLast m2powers.dropLast
    simp [m1length, m2length] at ih
    have m1structure : m1powers ≠ [] := by grind
    have m2structure : m2powers ≠ [] := by grind
    have m1structure := List.dropLast_concat_getLast m1structure
    have m2structure := List.dropLast_concat_getLast m2structure
    rw [← m1structure, ← m2structure]
    simp
    rw [List.zipWith_append]
    simp [Semiring.pow_add, ih]
    grind
    simp [m1length, m2length]

/-- Multiplying monomials denotes as a product, as long as the packed degrees
do not overflow a digit.  The check is `Polynomial.mulOk`. -/
theorem denote_mul {ctx : Context R} {m1 m2 : Mon n}
    (h1 : m1.WF) (h2 : m2.WF) (hlt : m1.degree + m2.degree < base n)
  : (m1.mul m2).denote ctx = m1.denote ctx * m2.denote ctx := by
  simp only [denote]
  rw [powers_mul h1 h2 hlt]
  exact denote_zipWith ctx n m1.powers m2.powers (by simp) (by simp)

theorem denote_mulVarPower (ctx : Context R) (m : Mon n) (i : Fin n) (k : Nat)
    (hk : k < base n) (hm : m.WF) (hlt : k + m.degree < base n)
  : denote (n := n) ctx (m.mulVarPower i k) = (ctx[i])^k * m.denote (n := n) ctx := by
  unfold mulVarPower
  have hwf : (fromVarPower i k).WF :=
    wf_ofPowersN (by simp) (by rw [sum_ofFn_oneHot]; exact hk)
  have hdeg : (fromVarPower i k).degree = k := by
    rw [degree, powers_fromVarPower i k hk, sum_ofFn_oneHot]
  rw [denote_mul hwf hm (by rw [hdeg]; exact hlt), denote_fromVarPower _ _ _ hk]

@[simp]
theorem mul_unit (m1 : Mon n) : m1.mul unit = m1 := by
  rw [← key_eq_iff_eq, mul_key, unit_key]
  omega

@[simp]
theorem unit_mul (m1 : Mon n) : unit.mul m1 = m1 := by
  rw [← key_eq_iff_eq, mul_key, unit_key]
  omega

/-- Compute `Mon.powers` on a literal key, so that `simp [Mon.denote]` can
still unfold the denotation of a concrete monomial. -/
simproc_decl mon_powers_simproc (Mon.powers ⟨_⟩) := fun e => do
  let_expr Mon.powers nExpr m ← e | return .continue
  let .some n ← getNatValue? (← whnf nExpr) | return .continue
  let_expr Mon.mk _ keyExpr ← (← whnf m) | return .continue
  let .some key ← getNatValue? (← whnf keyExpr) | return .continue
  let b := 2 ^ (max 8 (62 / max 1 n))
  let mut k := key
  let mut prev := 0
  let mut out : Array Lean.Expr := #[]
  for _ in [0:n] do
    let d := k % b
    out := out.push (mkNatLit (d - prev))
    prev := d
    k := k / b
  let lst ← mkListLit Nat.mkType out.toList
  pure <| .visit {expr := lst}

end Mon

namespace Polynomial

/-!
## Lemmas about grevlex for polynomials
-/

@[simp]
theorem not_Grevlex_zero_zero {R : Type} {n : Nat} [Zero R] : ¬ zero.Grevlex (zero (R := R) (n := n)) := by
  simp [Grevlex, grevlex, zero, grevlexTerms]

instance : @Trans (Polynomial R n) _ _ Grevlex Grevlex Grevlex where
  trans hab hbc := by
    expose_names
    simp [Grevlex, grevlex] at ⊢ hab hbc
    generalize a.terms = aterms at *
    generalize b.terms = bterms at *
    generalize c.terms = cterms at *
    fun_induction grevlexTerms aterms cterms generalizing bterms
    any_goals
      cases bterms
      all_goals
        contradiction
    case case3 =>
      trivial
    case case4 ahead atail chead ctail headOrdH ih =>
      cases bterms
      case nil => contradiction
      case cons bhead btail =>
        simp at headOrdH
        simp [grevlexTerms] at hab hbc
        by_cases bhead.monomial = ahead.monomial
        case pos h =>
          simp [h,← headOrdH] at hab hbc
          exact ih _ hab hbc
        case neg h =>
          simp [← headOrdH] at hbc
          rw [← Mon.eq_of_grevlex] at h
          simp [← Mon.grevlex_flip] at hbc
          simp [hbc] at hab
    case case5 ahead atail chead ctail headOrdH =>
      cases bterms
      case nil => contradiction
      case cons bhead btail =>
        simp at headOrdH
        simp [grevlexTerms] at hab hbc
        by_cases ahead.monomial = bhead.monomial
        case pos h =>
          simp [h] at headOrdH ⊢
          simp [h, headOrdH] at hab hbc
          trivial
        case neg h =>
          rw [← Mon.eq_of_grevlex] at h
          simp at hab
          split at hbc
          case h_1 heq =>
            simp at heq
            simp [heq] at hab
            trivial
          case h_2 =>
            simp [← Mon.grevlex_iff_grevlex_gt] at hab hbc ⊢
            exact Trans.trans hab hbc

/--
  Grevlex is decidable
-/
instance : @DecidableRel (Polynomial R n) (Polynomial R n) Grevlex :=
  fun m1 m2 => match h : grevlex m1 m2 with
  | .gt => .isTrue (by simp [h, Grevlex])
  | .eq => .isFalse (by simp [h, Grevlex])
  | .lt => .isFalse (by simp [h, Grevlex])

/--
  Grevlex is asymetric
-/
instance : @Std.Asymm (Polynomial R n) Grevlex where
  asymm a b abh := by
    simp [Grevlex, grevlex] at ⊢ abh
    generalize a.terms = aterms at *
    generalize b.terms = bterms at *

    induction aterms generalizing bterms
    case nil =>
      unfold grevlexTerms at abh
      split at abh
      all_goals
        contradiction
    case cons ih =>
      cases bterms
      case nil =>
        unfold grevlexTerms
        trivial
      case cons =>
        unfold grevlexTerms at ⊢ abh
        split
        case h_1 heq =>
          simp at heq
          simp [heq] at abh
          simp [*]
        case h_2 h =>
          simp at h
          split at abh
          case h_1 h2 =>
            simp at h2
            simp [h2]
          case h_2 =>
            simp [← Mon.grevlex_iff_grevlex_gt] at ⊢ abh
            simp [abh, Std.Asymm.asymm]


/--
  Grevlex is irreflexive
-/
instance : @Std.Irrefl (Polynomial R n) Grevlex where
  irrefl a := by
    simp [Grevlex, grevlex]
    induction a.terms
    case nil =>
      simp [grevlexTerms]
    case cons ih =>
      unfold grevlexTerms
      split
      case h_1 =>
        exact ih
      case h_2 h =>
        simp


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

/-! ## Simp Lemmas for mergeTerms

`mergeTerms` is `mergeTermsF` at a large constant fuel, and `mergeTermsF` is
structurally recursive so the kernel can evaluate it.  Since the fuel-0 case
falls back on `mergeTermsSpec`, the two agree at *every* fuel, so none of the
lemmas below carries a fuel side condition.
-/

theorem mergeTermsSpec_nil_right (xs : List (PolyTerm R n)) :
    mergeTermsSpec xs [] = xs := by
  cases xs
  case nil => simp [mergeTermsSpec]
  case cons head tail => simp [mergeTermsSpec, mergeTermsSpec.takeTillGE]

/-- The three-way defining equation of the reference merge. -/
theorem mergeTermsSpec_cons_cons (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) :
    mergeTermsSpec (x :: xs) (y :: ys) =
      match x.monomial.grevlex y.monomial with
      | .gt => x :: mergeTermsSpec xs (y :: ys)
      | .eq => ⟨x.coefficient + y.coefficient, x.monomial⟩ :: mergeTermsSpec xs ys
      | .lt => y :: mergeTermsSpec (x :: xs) ys := by
  cases h : x.monomial.grevlex y.monomial <;>
    simp only [h, mergeTermsSpec, mergeTermsSpec.takeTillGE]

theorem mergeTermsF_cons_cons (f : Nat) (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) :
    mergeTermsF (f + 1) (x :: xs) (y :: ys) =
      match x.monomial.grevlex y.monomial with
      | .gt => x :: mergeTermsF f xs (y :: ys)
      | .eq => ⟨x.coefficient + y.coefficient, x.monomial⟩ :: mergeTermsF f xs ys
      | .lt => y :: mergeTermsF f (x :: xs) ys := rfl

/-- Fuel is irrelevant: at every amount, `mergeTermsF` computes the reference
merge. -/
theorem mergeTermsF_eq_spec (f : Nat) :
    ∀ xs ys : List (PolyTerm R n), mergeTermsF f xs ys = mergeTermsSpec xs ys := by
  induction f with
  | zero => intro xs ys; rfl
  | succ f ih =>
    intro xs ys
    match xs, ys with
    | [], ys => simp [mergeTermsF, mergeTermsSpec]
    | x :: xs, [] =>
      rw [show mergeTermsF (f + 1) (x :: xs) [] = x :: xs from rfl,
        mergeTermsSpec_nil_right]
    | x :: xs, y :: ys =>
      rw [mergeTermsF_cons_cons, ih xs (y :: ys), ih xs ys, ih (x :: xs) ys,
        mergeTermsSpec_cons_cons]

theorem mergeTerms_eq_spec (xs ys : List (PolyTerm R n)) :
    mergeTerms xs ys = mergeTermsSpec xs ys := mergeTermsF_eq_spec _ xs ys

@[simp]
theorem mergeTerms_nil_left (xs : List (PolyTerm R n)) :
    mergeTerms [] xs = xs := by simp [mergeTerms_eq_spec, mergeTermsSpec]

@[simp]
theorem mergeTerms_nil_right (xs : List (PolyTerm R n)) :
    mergeTerms xs [] = xs := by
  rw [mergeTerms_eq_spec, mergeTermsSpec_nil_right]

/-- The three-way defining equation of the merge, stated for `mergeTerms`. -/
theorem mergeTerms_cons_cons (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) :
    mergeTerms (x :: xs) (y :: ys) =
      match x.monomial.grevlex y.monomial with
      | .gt => x :: mergeTerms xs (y :: ys)
      | .eq => ⟨x.coefficient + y.coefficient, x.monomial⟩ :: mergeTerms xs ys
      | .lt => y :: mergeTerms (x :: xs) ys := by
  simp only [mergeTerms_eq_spec]
  exact mergeTermsSpec_cons_cons x y xs ys

@[simp]
theorem mergeTerms_cons_cons_grevlex (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) (h : x.monomial.Grevlex y.monomial) :
    mergeTerms (x :: xs) (y :: ys) = x :: mergeTerms xs (y :: ys) := by
  simp [Mon.grevlex_iff_grevlex_gt] at h
  rw [mergeTerms_cons_cons, h]

@[simp]
theorem mergeTerms_cons_cons_rev_grevlex (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) (h : y.monomial.Grevlex x.monomial) :
    mergeTerms (x :: xs) (y :: ys) = y :: mergeTerms (x :: xs) ys := by
  simp [Mon.grevlex_iff_grevlex_gt, ← Mon.grevlex_flip] at h
  rw [mergeTerms_cons_cons, h]

@[simp]
theorem mergeTerms_cons_cons_eq (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) (h : y.monomial = x.monomial) :
    mergeTerms (x :: xs) (y :: ys) = ⟨x.coefficient + y.coefficient, x.monomial⟩ :: mergeTerms xs ys := by
  have h' : x.monomial.grevlex y.monomial = .eq := by simp [h]
  rw [mergeTerms_cons_cons, h']

theorem mergeTerms_symm (xs ys : List (PolyTerm R n)) : mergeTerms xs ys = mergeTerms ys xs := by
  induction xs generalizing ys
  case nil =>
    simp
  case cons head tail ih =>
    induction ys
    case nil =>
      simp
    case cons yhead ytail ih2 =>
      cases h : head.monomial.grevlex yhead.monomial
      case lt =>
        have h' : yhead.monomial.Grevlex head.monomial := by
          simp [Mon.grevlex_iff_grevlex_gt, ← Mon.grevlex_flip, h]
        rw [mergeTerms_cons_cons_rev_grevlex _ _ _ _ h',
          mergeTerms_cons_cons_grevlex _ _ _ _ h', ih2]
      case eq =>
        simp at h
        rw [mergeTerms_cons_cons_eq _ _ _ _ h.symm, mergeTerms_cons_cons_eq _ _ _ _ h]
        simp [h, Semiring.add_comm, ih]
      case gt =>
        have h' : head.monomial.Grevlex yhead.monomial := by
          simp [Mon.grevlex_iff_grevlex_gt, h]
        rw [mergeTerms_cons_cons_grevlex _ _ _ _ h',
          mergeTerms_cons_cons_rev_grevlex _ _ _ _ h', ih]

@[simp]
theorem mergeTerms_singleton_left (x : PolyTerm R n) (ys : List (PolyTerm R n)) :
    mergeTerms [x] ys = insertTerm x ys := by
  induction ys
  case nil =>
    simp
  case cons head tail ih =>
    cases h : x.monomial.grevlex head.monomial
    case lt =>
      have h' : head.monomial.Grevlex x.monomial := by
        simp [Mon.grevlex_iff_grevlex_gt, ← Mon.grevlex_flip, h]
      rw [mergeTerms_cons_cons_rev_grevlex _ _ _ _ h', ih,
        insertTerm_cons_grevlex_rev _ _ _ h']
    case eq =>
      simp at h
      rw [mergeTerms_cons_cons_eq _ _ _ _ h.symm, insertTerm_cons_eq _ _ _ h]
      simp
    case gt =>
      have h' : x.monomial.Grevlex head.monomial := by
        simp [Mon.grevlex_iff_grevlex_gt, h]
      rw [mergeTerms_cons_cons_grevlex _ _ _ _ h', insertTerm_cons_grevlex _ _ _ h']
      simp

@[simp]
theorem mergeTerms_singleton_right (y : PolyTerm R n) (xs : List (PolyTerm R n)) :
    mergeTerms xs [y] = insertTerm y xs := by
  rw [mergeTerms_symm]
  simp

theorem mergeTerms_mon_mem {xs ys : List (PolyTerm R n)} (tmem : t ∈ mergeTerms xs ys) :
    (∃ x ∈ xs, t.monomial = x.monomial) ∨ (∃ y ∈ ys, t.monomial = y.monomial) := by
  induction xs generalizing ys with
  | nil =>
    simp at tmem
    right
    exists t
  | cons xhead xtail ih1 =>
    induction ys with
    | nil =>
      simp at tmem
      cases tmem with
      | inl h => simp [h]
      | inr h =>
        left
        exists t
        simp [h]
    | cons yhead ytail ih2 =>
      cases grevlexH : xhead.monomial.grevlex yhead.monomial with
      | lt =>
        simp [Mon.grevlex_flip, ← Mon.grevlex_iff_grevlex_gt] at grevlexH
        simp [grevlexH] at tmem
        -- Working with or statements seems very awkward like this, is there a better way?
        cases tmem with
        | inl h => simp [h]
        | inr h =>
          simp [h] at ih2
          cases ih2 with
          | inl h' => simp [h']
          | inr h' => simp [h']
      | eq =>
        simp at grevlexH
        simp [grevlexH] at tmem
        cases tmem with
        | inl h => simp [h]
        | inr h =>
          specialize ih1 h
          cases ih1 with
          | inl h' => simp [h']
          | inr h' => simp [h']
      | gt =>
        simp [← Mon.grevlex_iff_grevlex_gt] at grevlexH
        simp [grevlexH] at tmem
        cases tmem with
        | inl h => simp [h]
        | inr h =>
          specialize ih1 h
          cases ih1 with
          | inl h' => simp [h']
          | inr h' => right; exact h'

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
        rw [mergeTerms_cons_cons] at mergeH
        split at mergeH
        all_goals
          simp at mergeH
  case mpr =>
    simp
    intro hx hy
    simp [hx, hy]

/-!
## Simp lemmas for removeZeros
-/
@[simp]
theorem removeZeros_nil [BEq R] : removeZeros ([] : List (PolyTerm R n)) = [] := by
  simp [removeZeros]

@[simp]
theorem removeZeros_cons_zero [BEq R] [LawfulBEq R] (x : PolyTerm R n) (xs : List (PolyTerm R n)) (h : x.coefficient = 0) :
    removeZeros (x :: xs) = removeZeros xs := by
  simp [removeZeros, h]

@[simp]
theorem removeZeros_cons_nonzero [BEq R] [LawfulBEq R] (x : PolyTerm R n) (xs : List (PolyTerm R n)) (h : x.coefficient ≠ 0) :
    removeZeros (x :: xs) = x :: removeZeros xs := by
  simp [removeZeros, h]

/-!
## Simp lemmas for mulMonTerms
-/

@[simp]
theorem mulMonTerms_nil (c : R) (m : Mon n) : mulMonTerms c m [] = [] := by simp [mulMonTerms]

@[simp]
theorem mulMonTerms_cons (c : R) (m : Mon n) (x : PolyTerm R n) (xs : List (PolyTerm R n)) :
  mulMonTerms c m (x :: xs) = ⟨c * x.coefficient, m.mul x.monomial⟩ :: mulMonTerms c m xs := by
  simp [mulMonTerms]

/-!
## Simp lemmas for mulTerms
-/

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
theorem mulTerms_cons_cons (x y : PolyTerm R n) (xs ys : List (PolyTerm R n)) :
  mulTerms (x :: xs) (y :: ys) = ⟨x.coefficient * y.coefficient, x.monomial.mul y.monomial⟩ ::
    mergeTerms (mulMonTerms x.coefficient x.monomial ys) (mulTerms xs (y::ys)) := by
  simp [mulTerms]


-- @[simp]
-- theorem mulTerms_cons_left (x : PolyTerm R n) (xs ys : List (PolyTerm R n))
--   (xsorted : Sorted (x :: xs)) (ysorted : Sorted ys)
--   : mulTerms (x :: xs) ys = mergeTerms (mulMonTerms x.coefficient x.monomial ys) (mulTerms xs ys) := by
--   sorry

-- @[simp]
-- theorem mulTerms_cons_right (y : PolyTerm R n) (xs ys : List (PolyTerm R n))
--   (xsorted : Sorted xs) (ysorted : Sorted (y :: ys))
--   : mulTerms xs (y :: ys) = mergeTerms (mulMonTerms y.coefficient y.monomial xs) (mulTerms xs ys) := by sorry


section Theorems
-- variable [deceq : DecidableEq R] [lawfuleq : LawfulBEq R]
open Grind.Semiring Grind.Ring Grind.CommSemiring
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast

/-! ## Sortedness preservation -/

omit inst in
private theorem Sorted_tail {t : PolyTerm R n} {ts : List (PolyTerm R n)}
    (h : Sorted (t :: ts)) : Sorted ts := (List.pairwise_cons.mp h).2

omit inst in
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

omit inst in
@[simp]
theorem sorted_cons {x : PolyTerm R n} :
    Sorted (x::xs) ↔ (∀ y ∈ xs, x.monomial.Grevlex y.monomial) ∧ Sorted xs := by
  simp [Sorted,List.pairwise_cons]

omit inst in
@[simp]
theorem sorted_nil : @Sorted n R [] := .nil

@[simp]
theorem sorted_singleton : Sorted [x] := by simp [Sorted]

omit inst in
@[simp high]
theorem sorted_cons_with_trans {x1 x2 : PolyTerm R n} {xs : List (PolyTerm R n) }:
    Sorted (x1::x2::xs) ↔ x1.monomial.Grevlex x2.monomial ∧ Sorted (x2 :: xs) := by
  simp
  intro sortedHyp1 sortedHyp2 x1x2Ord a amem
  specialize sortedHyp1 a amem
  exact Trans.trans x1x2Ord sortedHyp1

omit inst in
theorem isSorted_iff_sorted (terms : List (PolyTerm R n)) :
    isSorted terms = true ↔ Sorted terms := by
  induction terms
  case nil =>
    simp [isSorted, Sorted]
  case cons head tail ih  =>
    cases tail
    case nil =>
      simp [isSorted]
    case cons =>
      simp [isSorted, -sorted_cons]
      rw [← Mon.grevlex_iff_grevlex_gt, ih]

instance : @DecidablePred (List (PolyTerm R n)) Sorted :=
  fun terms =>
    if h : isSorted terms
    then isTrue (by exact (isSorted_iff_sorted terms).mp h)
    else isFalse (by rwa [← isSorted_iff_sorted terms])

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


theorem sorted_remove_second : (Sorted (x1 :: x2 :: xtail)) → (Sorted (x1 :: xtail)) := by
  intro h
  simp at h
  simp [h.right.right]
  intro y hy
  calc
    Mon.Grevlex _ _ := h.left
    Mon.Grevlex _ _ := h.right.left y hy

omit inst in
theorem insertTerm_grevlex_head [CommRing R] :
  (grevlexTerms [x] ts = .gt) → (insertTerm (R := R) x ts) = x :: ts := by
  cases ts
  case nil =>
    simp
  case cons head tail =>
    simp [grevlexTerms]
    split
    case h_1 =>
      intro h
      cases tail
      all_goals
        contradiction
    case h_2 =>
      intro h
      simp [insertTerm, h]

@[simp]
theorem mergeTerms_cons_left {x : PolyTerm R n} {xs ys : List (PolyTerm R n)}
  (xsorted : Sorted (x :: xs)) (ysorted : Sorted ys)
  : mergeTerms (x :: xs) ys = insertTerm x (mergeTerms xs ys) := by
  induction xs generalizing ys
  case nil =>
    simp
  case cons xhead xtail ih1 =>
    --have ih1' := ih1 (sorted_remove_second xsorted)
    --clear ih1
    induction ys
    case nil =>
      simp at xsorted
      simp [xsorted]
    case cons yhead ytail ih2 =>
      cases h : x.monomial.grevlex yhead.monomial
      case lt =>
        simp [Mon.grevlex_flip, ← Mon.grevlex_iff_grevlex_gt] at h
        simp [h]
        have headOrdH : yhead.monomial.Grevlex xhead.monomial := by
          calc
            Mon.Grevlex _ _ := h
            Mon.Grevlex _ _ := (sorted_cons_with_trans.mp xsorted).left
        simp [headOrdH, h]
        apply ih2 (List.pairwise_cons.mp ysorted).right
      case eq =>
        simp at h
        simp [h]
        have headOrdH : yhead.monomial.Grevlex xhead.monomial := by
          simp [← h, sorted_cons_with_trans.mp xsorted]
        simp [headOrdH, h]
      case gt =>
        have h' := Mon.grevlex_iff_grevlex_gt.mpr h
        simp [h']
        apply Eq.symm
        apply insertTerm_grevlex_head
        cases headOrd : xhead.monomial.grevlex yhead.monomial
        case lt =>
          simp [Mon.grevlex_flip, ← Mon.grevlex_iff_grevlex_gt] at headOrd
          simp [headOrd, grevlexTerms,h]
        case eq =>
          simp at headOrd
          simp [headOrd, grevlexTerms, h]
        case gt =>
          simp [← Mon.grevlex_iff_grevlex_gt] at headOrd
          have xord := sorted_cons_with_trans.mp xsorted
          simp [Mon.grevlex_iff_grevlex_gt] at xord
          simp [headOrd, grevlexTerms, xord.left]


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
  simp [Sorted,mulMonTerms, List.pairwise_map, ← Mon.grevlex_mul_mono_left]
  exact hx

theorem mulMonTerms_mem (xs : List (PolyTerm R n)) (tmem : t ∈ mulMonTerms c m xs) :
    ∃ t' ∈ xs, t.monomial = m.mul t'.monomial := by
  induction xs with
  | nil =>
    contradiction
  | cons head tail ih =>
    simp at ⊢ tmem
    cases tmem with
    | inl h => simp [h]
    | inr h => simp [h, ih]

theorem mulTerms_mem (xs ys : List (PolyTerm R n)) (tmem : t ∈ mulTerms xs ys) :
    ∃ tx ∈ xs, ∃ ty ∈ ys, t.monomial = tx.monomial.mul ty.monomial := by
  induction xs generalizing t
  case nil => contradiction
  case cons ih1 =>
    simp
    induction ys
    case nil => contradiction
    case cons ih2 =>
      simp at tmem
      cases tmem with
      | inl h => simp [h]
      | inr h =>
        cases mergeTerms_mon_mem h with
        | inl h' =>
          have ⟨x,⟨xmemh, xmonh⟩⟩ := h'
          have ⟨x',x'h⟩ := mulMonTerms_mem _ xmemh
          left
          exists x'
          simp [xmonh, x'h]
        | inr h' =>
          have ⟨y,⟨ymemh, ymonh⟩⟩ := h'
          right
          specialize ih1 ymemh
          have ⟨tx, ⟨txmemh, txmonh⟩⟩ := ih1
          exists tx
          simp [txmemh, ymonh]
          simp at txmonh
          exact txmonh

theorem sorted_mulTerms (xs ys : List (PolyTerm R n)) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mulTerms xs ys) := by
  fun_induction mulTerms
  case case1 => trivial
  case case2 => simp [Sorted]
  case case3 cx mx xs' cy my ys' ysh ih =>
    simp [ysh, Sorted_tail hx] at ih
    simp at hx
    simp
    constructor
    case left =>
      intro y ymem
      cases mergeTerms_mon_mem ymem
      case inl h =>
        have ⟨x,h⟩ := h
        have ⟨t',h'⟩ := mulMonTerms_mem _ h.left
        simp [h.right, h'.right, ← Mon.grevlex_mul_mono_left]
        simp [ysh] at hy
        simp [hy.left, h'.left]
      case inr h =>
        have ⟨x, h⟩ := h
        have ⟨tx,⟨htx,⟨ty,hty⟩⟩⟩ := mulTerms_mem _ _ h.left
        simp [h.right, hty.right]
        cases hty.left
        case head =>
          simp [← Mon.grevlex_mul_mono_right, hx, htx]
        case tail hty' =>
          calc
            (mx.mul my).Grevlex (mx.mul ty.monomial) := by
              simp [ysh] at hy
              simp [← Mon.grevlex_mul_mono_left]
              exact hy.left _ hty'
            (mx.mul ty.monomial).Grevlex (tx.monomial.mul ty.monomial) := by
              simp [← Mon.grevlex_mul_mono_right]
              exact hx.left _ htx
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
    induction ys
    case nil =>
      simp [Semiring.add_zero]
    case cons yhead ytail ih2 =>
      rw [mergeTerms_cons_cons]
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

theorem denote_smul (ctx : Context R) (c : R) (p : Polynomial R n) :
    denote ctx (smul c p) = c * denote ctx p := by simp [smul, denote, denoteTerms_map_smul, denoteTerms_removeZeros]

/--
Every monomial of `ts` is packed faithfully and has total degree at most `d`.
This is what `Polynomial.mulOk` checks, and what the product denotation lemmas
below need: it is exactly the region on which packed multiplication is
faithful.
-/
def TermsOk (d : Nat) (ts : List (PolyTerm R n)) : Prop :=
  ∀ t ∈ ts, t.monomial.WF ∧ t.monomial.degree ≤ d

omit beq lawfulbeq inst in
theorem TermsOk.tail {d : Nat} {t : PolyTerm R n} {ts : List (PolyTerm R n)}
    (h : TermsOk d (t :: ts)) : TermsOk d ts := fun u hu => h u (by simp [hu])

omit beq lawfulbeq inst in
theorem TermsOk.head {d : Nat} {t : PolyTerm R n} {ts : List (PolyTerm R n)}
    (h : TermsOk d (t :: ts)) : t.monomial.WF ∧ t.monomial.degree ≤ d := h t (by simp)

omit beq lawfulbeq inst in
/-- The kernel's `Bool` check implies the propositional side condition. -/
theorem termsOk_of_monWFB : ∀ {ts : List (PolyTerm R n)}, monWFB ts = true →
    TermsOk (monDegBound ts) ts := by
  intro ts
  induction ts with
  | nil => intro _ t ht; simp at ht
  | cons t ts ih =>
    intro h u hu
    simp only [monWFB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨Mon.wf_iff.mp h.1, by simp only [monDegBound]; omega⟩
    · have hrec := ih h.2 u hu
      refine ⟨hrec.1, ?_⟩
      have : monDegBound (t :: ts) = max t.monomial.degree (monDegBound ts) := rfl
      omega

omit beq lawfulbeq in
theorem denoteTerms_map_mulMon (ctx : Context R) (c : R) (m : Mon n)
    {d₁ d₂ : Nat} (hm : m.WF) (hmd : m.degree ≤ d₁) (hlt : d₁ + d₂ < Mon.base n) :
    ∀ (ts : List (PolyTerm R n)), TermsOk d₂ ts →
      denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, m.mul t.monomial⟩) =
        c * m.denote ctx * denoteTerms ctx ts := by
  intro ts
  induction ts with
  | nil => intro _; simp [mul_zero]
  | cons t ts ih =>
    intro hts
    have ht := hts.head
    simp only [List.map_cons, denoteTerms_cons, ih hts.tail]
    rw [left_distrib, mul_assoc, mul_assoc]; congr 1
    ac_nf
    congr
    exact Macaulean.Mon.denote_mul hm ht.1 (by have := ht.2; omega)

omit beq lawfulbeq in
theorem denoteTerms_mulMonTerms (ctx : Context R) (c : R) (m : Mon n)
    (p : List (PolyTerm R n)) {d₁ d₂ : Nat} (hm : m.WF) (hmd : m.degree ≤ d₁)
    (hp : TermsOk d₂ p) (hlt : d₁ + d₂ < Mon.base n) :
    denoteTerms ctx (mulMonTerms c m p) = c * m.denote ctx * denoteTerms ctx p := by
  simp only [mulMonTerms]
  exact denoteTerms_map_mulMon ctx c m hm hmd hlt p hp

omit beq lawfulbeq in
theorem denoteTerms_mulTerms (ctx : Context R) {d₁ d₂ : Nat} (hlt : d₁ + d₂ < Mon.base n) :
    ∀ (xs ys : List (PolyTerm R n)), TermsOk d₁ xs → TermsOk d₂ ys →
      denoteTerms ctx (mulTerms xs ys) = denoteTerms ctx xs * denoteTerms ctx ys := by
  intro xs
  induction xs with
  | nil => intro ys _ _; simp [Semiring.zero_mul]
  | cons x xs ih =>
    intro ys hx hy
    cases ys with
    | nil => simp [Semiring.mul_zero]
    | cons y ys =>
      have hxx := hx.head
      have hyy := hy.head
      rw [mulTerms_cons_cons]
      simp only [denoteTerms_cons, denoteTerms_mergeTerms]
      rw [denoteTerms_mulMonTerms ctx x.coefficient x.monomial ys hxx.1 hxx.2 hy.tail hlt,
        ih (y :: ys) hx.tail hy,
        Mon.denote_mul hxx.1 hyy.1 (by have := hxx.2; have := hyy.2; omega)]
      simp only [denoteTerms_cons, Semiring.right_distrib, Semiring.left_distrib]
      ac_nf

theorem denote_mul (ctx : Context R) (p q : Polynomial R n) {d₁ d₂ : Nat}
    (hp : TermsOk d₁ p.terms) (hq : TermsOk d₂ q.terms) (hlt : d₁ + d₂ < Mon.base n) :
    denote ctx (mul p q) = denote ctx p * denote ctx q := by
  unfold denote Polynomial.mul
  simp only [denoteTerms_removeZeros]
  exact denoteTerms_mulTerms ctx hlt p.terms q.terms hp hq

theorem denote_mulChecked (ctx : Context R) {p q r : Polynomial R n}
    (h : mulChecked p q = some r) : denote ctx r = denote ctx p * denote ctx q := by
  unfold mulChecked at h
  split at h
  · rename_i hok
    cases h
    simp only [mulOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact denote_mul ctx p q (termsOk_of_monWFB hok.1.1) (termsOk_of_monWFB hok.1.2) hok.2
  · exact absurd h (by simp)

omit beq lawfulbeq in
theorem denote_singleton (ctx : Context R) (i : Fin n)
  : denote ctx (ofTerm ⟨c, Mon.fromVar (n := n) i⟩) = c * (ctx.get i):= by
  simp [denote, ofTerm]
  conv =>
    lhs
    left
    right
    apply Mon.denote_fromVar ctx
  simp [getElem, Semiring.add_zero]

omit beq lawfulbeq in
theorem denote_singleton_no_constant (ctx : Context R) (x : R) (i : Fin n) (h2 : ctx.get i = x) : denote ctx (ofVar i) = x := by
  simp [denote, ofVar, ofTerm]
  conv =>
    lhs
    left
    right
    apply Mon.denote_fromVar ctx
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
    (tg : PolyTerm R n) (g' : List (PolyTerm R n))
    {d₁ d₂ : Nat} (hf : TermsOk d₁ (tf :: f')) (hg : TermsOk d₂ (tg :: g'))
    (hlt : d₁ + d₂ < Mon.base n) :
    denote ctx (mul ⟨tf :: f'⟩ ⟨tg :: g'⟩) =
      tf.coefficient * tg.coefficient * (tf.monomial.mul tg.monomial).denote ctx
      + tf.coefficient * tf.monomial.denote ctx * denoteTerms ctx g'
      + denoteTerms ctx f' * tg.coefficient * tg.monomial.denote ctx
      + denoteTerms ctx f' * denoteTerms ctx g' := by
  rw [denote_mul ctx _ _ hf hg hlt]; simp only [denote_mk, denoteTerms_cons]; rw [foil]
  ac_nf
  simp [Mon.denote_mul hf.head.1 hg.head.1
    (by have := hf.head.2; have := hg.head.2; omega)]

end Theorems
end Polynomial

end Macaulean
