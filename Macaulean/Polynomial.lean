/-
  New polynomial representation for Macaulean.

  Polynomials as sorted lists of coefficient-monomial pairs, using
  Grind.CommRing.Mon for monomials in strictly decreasing grevlex order.
-/
import Lean
open Lean Grind CommRing
namespace Macaulean

structure PolyTerm (R : Type) where
  coefficient : R
  monomial : Mon
  deriving Repr, Inhabited, BEq

structure Polynomial (R : Type) where
  terms : List (PolyTerm R)
  deriving Repr, Inhabited, BEq

namespace Polynomial

def zero : Polynomial R := ⟨[]⟩

def ofTerm (t : PolyTerm R) : Polynomial R := ⟨[t]⟩

def Sorted : List (PolyTerm R) → Prop
  | [] => True
  | [_] => True
  | t₁ :: t₂ :: ts => t₁.monomial.grevlex t₂.monomial = .gt ∧ Sorted (t₂ :: ts)

def isSorted : List (PolyTerm R) → Bool
  | [] => true
  | [_] => true
  | t₁ :: t₂ :: ts => t₁.monomial.grevlex t₂.monomial == .gt && isSorted (t₂ :: ts)

def denoteTerms [Grind.CommRing R] (ctx : Context R) : List (PolyTerm R) → R
  | [] => 0
  | t :: ts => t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts

def denote [Grind.CommRing R] (ctx : Context R) (p : Polynomial R) : R :=
  denoteTerms ctx p.terms

def insertTerm [Grind.CommRing R] [DecidableEq R]
    (c : R) (m : Mon) (ts : List (PolyTerm R)) : List (PolyTerm R) :=
  match ts with
  | [] => if c = 0 then [] else [⟨c, m⟩]
  | t :: rest =>
    match m.grevlex t.monomial with
    | .gt => if c = 0 then t :: rest else ⟨c, m⟩ :: t :: rest
    | .eq =>
      let c' := c + t.coefficient
      if c' = 0 then rest else ⟨c', m⟩ :: rest
    | .lt => t :: insertTerm c m rest

def addTerm [Grind.CommRing R] [DecidableEq R]
    (p : Polynomial R) (c : R) (m : Mon) : Polynomial R :=
  ⟨insertTerm c m p.terms⟩

def mergeTerms [Grind.CommRing R] [DecidableEq R]
    (xs ys : List (PolyTerm R)) : List (PolyTerm R) :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs', y :: ys' =>
    match x.monomial.grevlex y.monomial with
    | .gt => x :: mergeTerms xs' (y :: ys')
    | .eq =>
      let c := x.coefficient + y.coefficient
      if c = 0 then mergeTerms xs' ys'
      else ⟨c, x.monomial⟩ :: mergeTerms xs' ys'
    | .lt => y :: mergeTerms (x :: xs') ys'
termination_by xs.length + ys.length

def add [Grind.CommRing R] [DecidableEq R] (p q : Polynomial R) : Polynomial R :=
  ⟨mergeTerms p.terms q.terms⟩

instance [Grind.CommRing R] [DecidableEq R] : Add (Polynomial R) := ⟨add⟩

def smul [Grind.CommRing R] (c : R) (p : Polynomial R) : Polynomial R :=
  ⟨p.terms.map fun t => ⟨c * t.coefficient, t.monomial⟩⟩

def mulMon [Grind.CommRing R] (c : R) (m : Mon) (p : Polynomial R) : Polynomial R :=
  ⟨p.terms.map fun t => ⟨c * t.coefficient, m.mul t.monomial⟩⟩

def mulTerms [Grind.CommRing R] [DecidableEq R]
    (ts : List (PolyTerm R)) (q : Polynomial R) : Polynomial R :=
  match ts with
  | [] => zero
  | t :: rest => add (mulMon t.coefficient t.monomial q) (mulTerms rest q)

def mul [Grind.CommRing R] [DecidableEq R] (p q : Polynomial R) : Polynomial R :=
  mulTerms p.terms q

instance [Grind.CommRing R] [DecidableEq R] : Mul (Polynomial R) := ⟨mul⟩

def neg [Neg R] (p : Polynomial R) : Polynomial R :=
  ⟨p.terms.map fun t => ⟨-t.coefficient, t.monomial⟩⟩

instance [Neg R] : Neg (Polynomial R) := ⟨neg⟩

def sub [Grind.CommRing R] [DecidableEq R] (p q : Polynomial R) : Polynomial R :=
  add p (neg q)

instance [Grind.CommRing R] [DecidableEq R] : Sub (Polynomial R) := ⟨sub⟩

def leadTerm (p : Polynomial R) : Option (PolyTerm R) := p.terms.head?

def tail (p : Polynomial R) : Polynomial R := ⟨p.terms.tail⟩

def fromGrindPoly (p : CommRing.Poly) : Polynomial Int :=
  ⟨go p []⟩
where
  go : CommRing.Poly → List (PolyTerm Int) → List (PolyTerm Int)
    | .num k, acc => if k == 0 then acc else acc ++ [⟨k, .unit⟩]
    | .add k m p, acc => if k == 0 then go p acc else go p (acc ++ [⟨k, m⟩])

def fromGrindPolyAs [inst : Grind.CommRing R] (p : CommRing.Poly) : Polynomial R :=
  have : IntCast R := inst.toRing.intCast
  ⟨(fromGrindPoly p).terms.map fun t => ⟨Int.cast t.coefficient, t.monomial⟩⟩

/-! ## Denotation theorems -/

section Theorems
variable {R : Type} [inst : Grind.CommRing R] [deceq : DecidableEq R]
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
@[simp] theorem denote_mk (ctx : Context R) (ts : List (PolyTerm R)) :
    denote ctx ⟨ts⟩ = denoteTerms ctx ts := rfl

omit deceq in
@[simp] theorem denoteTerms_nil (ctx : Context R) :
    denoteTerms ctx ([] : List (PolyTerm R)) = 0 := rfl

omit deceq in
@[simp] theorem denoteTerms_cons (ctx : Context R) (t : PolyTerm R) (ts : List (PolyTerm R)) :
    denoteTerms ctx (t :: ts) = t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts := rfl

omit deceq in
theorem denote_zero (ctx : Context R) : denote ctx (zero : Polynomial R) = 0 := rfl

omit deceq in
theorem denote_cons_eq (ctx : Context R) (t : PolyTerm R) (ts : List (PolyTerm R)) :
    denote ctx ⟨t :: ts⟩ = t.coefficient * t.monomial.denote ctx + denote ctx ⟨ts⟩ := rfl

omit deceq in
@[simp] theorem denoteTerms_append (ctx : Context R) (xs ys : List (PolyTerm R)) :
    denoteTerms ctx (xs ++ ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  induction xs with
  | nil => exact (zero_add' _).symm
  | cons x xs ih => simp [ih, add_assoc]

omit deceq in
theorem denote_leadTerm_tail (ctx : Context R) (p : Polynomial R)
    (t : PolyTerm R) (ts : List (PolyTerm R)) (h : p.terms = t :: ts) :
    denote ctx p = t.coefficient * t.monomial.denote ctx + denote ctx p.tail := by
  simp [denote, tail, h]

theorem denoteTerms_insertTerm (ctx : Context R) (c : R) (m : Mon) (ts : List (PolyTerm R)) :
    denoteTerms ctx (insertTerm c m ts) = c * m.denote ctx + denoteTerms ctx ts := by
  induction ts with
  | nil => simp only [insertTerm]; split
           · next h => subst h; simp [zero_mul, zero_add']
           · simp [add_zero]
  | cons t rest ih =>
    simp only [insertTerm]; split
    · split
      · next h => subst h; simp [zero_mul, zero_add']
      · simp
    · next hg => have hm : m = t.monomial := Mon.eq_of_grevlex hg; split
                 · next hc => simp only [denoteTerms_cons]; rw [hm, ← add_assoc, ← right_distrib, hc, zero_mul, zero_add']
                 · simp only [denoteTerms_cons]; rw [hm, ← add_assoc, ← right_distrib]
    · simp only [denoteTerms_cons]; rw [ih, add_left_comm']

private theorem denoteTerms_mergeTerms_go (ctx : Context R) (n : Nat)
    (xs ys : List (PolyTerm R)) (hlen : xs.length + ys.length ≤ n) :
    denoteTerms ctx (mergeTerms xs ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  induction n generalizing xs ys with
  | zero => have hx : xs = [] := by cases xs <;> simp_all <;> grind
            subst hx; simp [mergeTerms, zero_add']
  | succ n ih =>
    match xs, ys with
    | [], ys => simp [mergeTerms, zero_add']
    | _ :: _, [] => simp [mergeTerms, add_zero]
    | x :: xs', y :: ys' =>
      simp only [mergeTerms]; split
      · rw [denoteTerms_cons, ih xs' (y :: ys') (by simp_all; grind), ← add_assoc]
        simp only [denoteTerms_cons]
      · next hg =>
        have hm := Mon.eq_of_grevlex hg
        split
        · next hc =>
          rw [ih xs' ys' (by simp_all; grind), denoteTerms_cons, denoteTerms_cons, hm]
          exact (add_cancel _ _ _ _ (by rw [← right_distrib, hc, zero_mul])).symm
        · rw [denoteTerms_cons, ih xs' ys' (by simp_all; grind),
              denoteTerms_cons, denoteTerms_cons, hm, right_distrib,
              add_assoc, add_left_comm' (y.coefficient * Mon.denote ctx y.monomial)
                (denoteTerms ctx xs'), ← add_assoc]
      · rw [denoteTerms_cons, ih (x :: xs') ys' (by simp_all; grind), add_left_comm']
        simp only [denoteTerms_cons]

theorem denoteTerms_mergeTerms (ctx : Context R) (xs ys : List (PolyTerm R)) :
    denoteTerms ctx (mergeTerms xs ys) = denoteTerms ctx xs + denoteTerms ctx ys :=
  denoteTerms_mergeTerms_go ctx _ xs ys (Nat.le_refl _)

theorem denote_add (ctx : Context R) (p q : Polynomial R) :
    denote ctx (add p q) = denote ctx p + denote ctx q :=
  denoteTerms_mergeTerms ctx p.terms q.terms

omit deceq in
theorem denoteTerms_map_smul (ctx : Context R) (c : R) (ts : List (PolyTerm R)) :
    denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, t.monomial⟩) = c * denoteTerms ctx ts := by
  induction ts with
  | nil => simp [mul_zero]
  | cons t ts ih => simp [ih, left_distrib, mul_assoc]

omit deceq in
theorem denote_smul (ctx : Context R) (c : R) (p : Polynomial R) :
    denote ctx (smul c p) = c * denote ctx p := by simp [smul, denote, denoteTerms_map_smul]

omit deceq in
theorem denoteTerms_map_mulMon (ctx : Context R) (c : R) (m : Mon) (ts : List (PolyTerm R)) :
    denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, m.mul t.monomial⟩) =
    c * m.denote ctx * denoteTerms ctx ts := by
  induction ts with
  | nil => simp [mul_zero]
  | cons t ts ih =>
    simp only [List.map_cons, denoteTerms_cons, ih, Mon.denote_mul]
    rw [left_distrib, mul_assoc, mul_assoc]; congr 1
    simp only [mul_assoc, @Grind.CommSemiring.mul_comm R _ (Mon.denote ctx m)]

omit deceq in
theorem denote_mulMon (ctx : Context R) (c : R) (m : Mon) (p : Polynomial R) :
    denote ctx (mulMon c m p) = c * m.denote ctx * denote ctx p := by
  simp [mulMon, denote, denoteTerms_map_mulMon]

theorem denote_mulTerms (ctx : Context R) (ts : List (PolyTerm R)) (q : Polynomial R) :
    denote ctx (mulTerms ts q) = denoteTerms ctx ts * denote ctx q := by
  induction ts with
  | nil => simp [mulTerms, denote_zero, zero_mul]
  | cons t ts ih =>
    simp only [mulTerms, denote_add, denote_mulMon, denoteTerms_cons, ih]
    rw [right_distrib, mul_assoc]

theorem denote_mul (ctx : Context R) (p q : Polynomial R) :
    denote ctx (mul p q) = denote ctx p * denote ctx q :=
  denote_mulTerms ctx p.terms q

omit deceq in
private theorem foil (a b c d : R) :
    (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [right_distrib, left_distrib, left_distrib]; simp only [add_assoc]

theorem mul_leadTerm_expand (ctx : Context R)
    (tf : PolyTerm R) (f' : List (PolyTerm R))
    (tg : PolyTerm R) (g' : List (PolyTerm R)) :
    denote ctx (mul ⟨tf :: f'⟩ ⟨tg :: g'⟩) =
      tf.coefficient * tg.coefficient * (tf.monomial.mul tg.monomial).denote ctx
      + tf.coefficient * tf.monomial.denote ctx * denoteTerms ctx g'
      + denoteTerms ctx f' * tg.coefficient * tg.monomial.denote ctx
      + denoteTerms ctx f' * denoteTerms ctx g' := by
  rw [denote_mul]; simp only [denote_mk, denoteTerms_cons]; rw [foil]
  congr 1; congr 1; congr 1
  · rw [Mon.denote_mul]; simp only [mul_assoc, @Grind.CommSemiring.mul_comm R _ (Mon.denote ctx tf.monomial)]
  · rw [← mul_assoc]

/-! ## Grevlex ordering properties -/

private theorem powerRevlex_swap (k₁ k₂ : Nat) :
    (powerRevlex k₁ k₂).swap = powerRevlex k₂ k₁ := by
  simp only [powerRevlex, Bool.cond_eq_ite]
  split <;> split <;> simp_all [Nat.blt_eq] <;> grind

private theorem nat_beq_comm (a b : Nat) : (a == b) = (b == a) := by
  simp [BEq.beq]; exact eq_comm

private theorem revlexWF_swap (m₁ m₂ : Mon) :
    (Mon.revlexWF m₁ m₂).swap = Mon.revlexWF m₂ m₁ := by
  fun_induction Mon.revlexWF m₁ m₂
  · simp [Mon.revlexWF]
  · simp [Mon.revlexWF]
  · simp [Mon.revlexWF]
  · next pw₁ m₁ pw₂ m₂ heq ih =>
    have heq' : (pw₂.x == pw₁.x) = true := by rw [nat_beq_comm]; exact heq
    simp only [Mon.revlexWF, heq', cond_true, Ordering.swap_then, ih, powerRevlex_swap]
  · next pw₁ m₁ pw₂ m₂ hne hblt ih =>
    have hne' : (pw₂.x == pw₁.x) = false := by rw [nat_beq_comm]; exact hne
    have hnblt' : (pw₂.x.blt pw₁.x) = false := by
      cases h : pw₂.x.blt pw₁.x
      · rfl
      · exfalso; exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.blt_eq.mp hblt) (Nat.blt_eq.mp h))
    simp only [Mon.revlexWF, hne', cond_false, hnblt']
    rw [Ordering.swap_then, ih]; simp [Ordering.swap]
  · next pw₁ m₁ pw₂ m₂ hne hnblt ih =>
    have hne' : (pw₂.x == pw₁.x) = false := by rw [nat_beq_comm]; exact hne
    have hblt' : (pw₂.x.blt pw₁.x) = true := by
      cases h : pw₂.x.blt pw₁.x
      · exfalso
        have h1 : ¬(pw₁.x < pw₂.x) := fun hlt => absurd (Nat.blt_eq.mpr hlt) (by simp_all)
        have h2 : ¬(pw₂.x < pw₁.x) := fun hlt => absurd (Nat.blt_eq.mpr hlt) (by simp_all)
        have : pw₁.x = pw₂.x := Nat.le_antisymm (Nat.le_of_not_gt h2) (Nat.le_of_not_gt h1)
        simp_all [BEq.beq]
      · rfl
    simp only [Mon.revlexWF, hne', cond_false, hblt', cond_true]
    rw [Ordering.swap_then, ih]; simp [Ordering.swap]

private theorem revlexFuel_swap (fuel : Nat) (m₁ m₂ : Mon) :
    (Mon.revlexFuel fuel m₁ m₂).swap = Mon.revlexFuel fuel m₂ m₁ := by
  fun_induction Mon.revlexFuel fuel m₁ m₂
  · simp [Mon.revlexFuel, revlexWF_swap]
  · simp [Mon.revlexFuel]
  · simp [Mon.revlexFuel]
  · simp [Mon.revlexFuel]
  · next fuel pw₁ m₁ pw₂ m₂ heq ih =>
    have heq' : (pw₂.x == pw₁.x) = true := by rw [nat_beq_comm]; exact heq
    simp only [Mon.revlexFuel, heq', cond_true, Ordering.swap_then, ih, powerRevlex_swap]
  · next fuel pw₁ m₁ pw₂ m₂ hne hblt ih =>
    have hne' : (pw₂.x == pw₁.x) = false := by rw [nat_beq_comm]; exact hne
    have hnblt' : (pw₂.x.blt pw₁.x) = false := by
      cases h : pw₂.x.blt pw₁.x
      · rfl
      · exfalso; exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.blt_eq.mp hblt) (Nat.blt_eq.mp h))
    simp only [Mon.revlexFuel, hne', cond_false, hnblt']
    rw [Ordering.swap_then, ih]; simp [Ordering.swap]
  · next fuel pw₁ m₁ pw₂ m₂ hne hnblt ih =>
    have hne' : (pw₂.x == pw₁.x) = false := by rw [nat_beq_comm]; exact hne
    have hblt' : (pw₂.x.blt pw₁.x) = true := by
      cases h : pw₂.x.blt pw₁.x
      · exfalso
        have h1 : ¬(pw₁.x < pw₂.x) := fun hlt => absurd (Nat.blt_eq.mpr hlt) (by simp_all)
        have h2 : ¬(pw₂.x < pw₁.x) := fun hlt => absurd (Nat.blt_eq.mpr hlt) (by simp_all)
        have : pw₁.x = pw₂.x := Nat.le_antisymm (Nat.le_of_not_gt h2) (Nat.le_of_not_gt h1)
        simp_all [BEq.beq]
      · rfl
    simp only [Mon.revlexFuel, hne', cond_false, hblt', cond_true]
    rw [Ordering.swap_then, ih]; simp [Ordering.swap]

private theorem revlex_swap (m₁ m₂ : Mon) :
    (Mon.revlex m₁ m₂).swap = Mon.revlex m₂ m₁ := revlexFuel_swap _ m₁ m₂

omit deceq in
private theorem grevlex_swap (m₁ m₂ : Mon) :
    (Mon.grevlex m₁ m₂).swap = Mon.grevlex m₂ m₁ := by
  simp only [Mon.grevlex, Ordering.swap_then, Nat.compare_swap]; congr 1; exact revlex_swap m₁ m₂

omit deceq in
private theorem grevlex_flip {m₁ m₂ : Mon} (h : m₁.grevlex m₂ = .lt) :
    m₂.grevlex m₁ = .gt := by
  have := grevlex_swap m₁ m₂; rw [h] at this; simpa using this.symm

omit deceq in
private theorem grevlex_gt_flip {m₁ m₂ : Mon} (h : m₁.grevlex m₂ = .gt) :
    m₂.grevlex m₁ = .lt := by
  have := grevlex_swap m₁ m₂; rw [h] at this; simpa using this.symm

/-- Transitivity of revlex ordering -- requires deep structural induction on Mon. -/
private theorem revlex_trans {m₁ m₂ m₃ : Mon}
    (h₁ : Mon.revlex m₁ m₂ = .gt) (h₂ : Mon.revlex m₂ m₃ = .gt) :
    Mon.revlex m₁ m₃ = .gt := by sorry

private theorem grevlex_trans {m₁ m₂ m₃ : Mon}
    (h₁ : m₁.grevlex m₂ = .gt) (h₂ : m₂.grevlex m₃ = .gt) :
    m₁.grevlex m₃ = .gt := by
  simp only [Mon.grevlex] at *
  rw [Ordering.then_eq_gt] at h₁ h₂ ⊢
  rcases h₁ with h₁d | ⟨h₁d, h₁r⟩ <;> rcases h₂ with h₂d | ⟨h₂d, h₂r⟩
  · left; simp [Nat.compare_eq_gt] at *; grind
  · left; simp [Nat.compare_eq_gt, Nat.compare_eq_eq] at *; grind
  · left; simp [Nat.compare_eq_gt, Nat.compare_eq_eq] at *; grind
  · right; exact ⟨by simp [Nat.compare_eq_eq] at *; grind, revlex_trans h₁r h₂r⟩

/-- Monotonicity of grevlex under monomial multiplication -- requires structural induction. -/
private theorem grevlex_mul_mono {m₁ m₂ m : Mon}
    (h : m₁.grevlex m₂ = .gt) : (m.mul m₁).grevlex (m.mul m₂) = .gt := by sorry

/-! ## Sortedness preservation -/

omit inst deceq in
private theorem Sorted_tail {t : PolyTerm R} {ts : List (PolyTerm R)}
    (h : Sorted (t :: ts)) : Sorted ts := by
  cases ts with
  | nil => exact True.intro
  | cons t' ts' => exact h.2

omit inst deceq in
private theorem Sorted_head_gt_all :
    ∀ (ts : List (PolyTerm R)) (t : PolyTerm R),
    Sorted (t :: ts) → ∀ t' ∈ ts, t.monomial.grevlex t'.monomial = .gt := by
  intro ts
  induction ts with
  | nil => intro _ _ _ h; exact absurd h List.not_mem_nil
  | cons u rest ih =>
    intro t hs t' ht'
    cases ht' with
    | head => exact hs.1
    | tail _ ht' =>
      exact grevlex_trans hs.1 (ih u (Sorted_tail hs) t' ht')

private theorem insertTerm_head_grevlex (c : R) (m : Mon) (ts : List (PolyTerm R))
    (t : PolyTerm R) (hgt : t.monomial.grevlex m = .gt)
    (hs : Sorted ts) (hs_hd : ∀ t' ∈ ts, t.monomial.grevlex t'.monomial = .gt) :
    ∀ r ∈ (insertTerm c m ts), t.monomial.grevlex r.monomial = .gt := by
  induction ts with
  | nil =>
    simp only [insertTerm]
    split
    · intro _ h; exact absurd h List.not_mem_nil
    · intro r hr; simp at hr; subst hr; exact hgt
  | cons u rest ih =>
    have hu_gt := hs_hd u List.mem_cons_self
    have hrest_gt : ∀ t' ∈ rest, t.monomial.grevlex t'.monomial = .gt :=
      fun t' ht' => hs_hd t' (List.mem_cons_of_mem u ht')
    simp only [insertTerm]
    split
    · -- m.grevlex u.monomial = .gt
      split
      · intro r hr; exact hs_hd r hr
      · intro r hr; simp at hr
        rcases hr with rfl | rfl | hr
        · exact hgt
        · exact hu_gt
        · exact hrest_gt r hr
    · -- m.grevlex u.monomial = .eq
      next heq =>
      have hm_eq : m = u.monomial := Mon.eq_of_grevlex heq
      split
      · intro r hr; exact hrest_gt r hr
      · intro r hr; simp at hr
        rcases hr with rfl | hr
        · rw [hm_eq]; exact hu_gt
        · exact hrest_gt r hr
    · -- m.grevlex u.monomial = .lt
      intro r hr; simp at hr
      rcases hr with rfl | hr
      · exact hu_gt
      · exact ih (Sorted_tail hs) hrest_gt r hr

theorem sorted_insertTerm (c : R) (m : Mon) (ts : List (PolyTerm R)) (hs : Sorted ts) :
    Sorted (insertTerm c m ts) := by
  induction ts with
  | nil =>
    simp only [insertTerm]
    split <;> exact True.intro
  | cons t rest ih =>
    have hs_rest := Sorted_tail hs
    simp only [insertTerm]
    split
    · -- m.grevlex t.monomial = .gt
      next hgt =>
      split
      · exact hs
      · exact ⟨hgt, hs⟩
    · -- m.grevlex t.monomial = .eq
      next heq =>
      have hm_eq : m = t.monomial := Mon.eq_of_grevlex heq
      split
      · exact hs_rest
      · cases rest with
        | nil => exact True.intro
        | cons t' rest' =>
          exact ⟨hm_eq ▸ hs.1, hs.2⟩
    · -- m.grevlex t.monomial = .lt
      next hlt =>
      have hgt_flip := grevlex_flip hlt
      have ih_result := ih hs_rest
      cases h : insertTerm c m rest with
      | nil => exact True.intro
      | cons r rest' =>
        constructor
        · have hr : r ∈ insertTerm c m rest := by rw [h]; exact List.mem_cons_self
          exact insertTerm_head_grevlex c m rest t hgt_flip hs_rest
            (Sorted_head_gt_all rest t hs) r hr
        · rw [h] at ih_result
          cases rest' with
          | nil => exact True.intro
          | cons _ _ => exact ih_result

private theorem mergeTerms_bound_go (n : Nat) (bound : Mon)
    (xs ys : List (PolyTerm R)) (hlen : xs.length + ys.length ≤ n)
    (hx : ∀ t ∈ xs, bound.grevlex t.monomial = .gt)
    (hy : ∀ t ∈ ys, bound.grevlex t.monomial = .gt) :
    ∀ r ∈ mergeTerms xs ys, bound.grevlex r.monomial = .gt := by
  induction n generalizing xs ys with
  | zero =>
    have : xs = [] := by cases xs <;> simp_all <;> grind
    subst this; simp only [mergeTerms]; exact hy
  | succ n ih =>
    match xs, ys, hx, hy, hlen with
    | [], _, _, hy, _ => simp only [mergeTerms]; exact hy
    | _ :: _, [], hx, _, _ => simp only [mergeTerms]; exact hx
    | x :: xs', y :: ys', hx, hy, hlen =>
      have hx_hd := hx x List.mem_cons_self
      have hy_hd := hy y List.mem_cons_self
      have hx_tl : ∀ t ∈ xs', bound.grevlex t.monomial = .gt :=
        fun t ht => hx t (List.mem_cons_of_mem x ht)
      have hy_tl : ∀ t ∈ ys', bound.grevlex t.monomial = .gt :=
        fun t ht => hy t (List.mem_cons_of_mem y ht)
      simp only [mergeTerms]; split
      · -- gt
        intro r hr; simp at hr
        rcases hr with rfl | hr
        · exact hx_hd
        · exact ih xs' (y :: ys') (by simp_all; grind) hx_tl hy r hr
      · -- eq
        split
        · exact ih xs' ys' (by simp_all; grind) hx_tl hy_tl
        · intro r hr; simp at hr
          rcases hr with rfl | hr
          · exact hx_hd
          · exact ih xs' ys' (by simp_all; grind) hx_tl hy_tl r hr
      · -- lt
        intro r hr; simp at hr
        rcases hr with rfl | hr
        · exact hy_hd
        · exact ih (x :: xs') ys' (by simp_all; grind) hx hy_tl r hr

private theorem sorted_mergeTerms_go (n : Nat)
    (xs ys : List (PolyTerm R)) (hlen : xs.length + ys.length ≤ n)
    (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mergeTerms xs ys) := by
  induction n generalizing xs ys with
  | zero =>
    have : xs = [] := by cases xs <;> simp_all <;> grind
    subst this; simp only [mergeTerms]; exact hy
  | succ n ih =>
    match xs, ys, hx, hy, hlen with
    | [], _, _, hy, _ => simp only [mergeTerms]; exact hy
    | _ :: _, [], hx, _, _ => simp only [mergeTerms]; exact hx
    | x :: xs', y :: ys', hx, hy, hlen =>
      simp only [mergeTerms]; split
      · -- x > y (gt case)
        next hgt =>
        have ih_sub := ih xs' (y :: ys') (by simp_all; grind) (Sorted_tail hx) hy
        cases h : mergeTerms xs' (y :: ys') with
        | nil => exact True.intro
        | cons r rest =>
          constructor
          · have hr : r ∈ mergeTerms xs' (y :: ys') := by rw [h]; exact List.mem_cons_self
            exact mergeTerms_bound_go _ x.monomial xs' (y :: ys') (Nat.le_refl _)
              (Sorted_head_gt_all xs' x hx)
              (fun t ht => by
                cases ht with
                | head => exact hgt
                | tail _ ht => exact grevlex_trans hgt (Sorted_head_gt_all ys' y hy t ht))
              r hr
          · rw [h] at ih_sub; exact ih_sub
      · -- x == y (eq case)
        next heq =>
        have hm_eq : x.monomial = y.monomial := Mon.eq_of_grevlex heq
        split
        · -- c = 0
          exact ih xs' ys' (by simp_all; grind) (Sorted_tail hx) (Sorted_tail hy)
        · -- c ≠ 0
          have ih_sub := ih xs' ys' (by simp_all; grind) (Sorted_tail hx) (Sorted_tail hy)
          cases h : mergeTerms xs' ys' with
          | nil => exact True.intro
          | cons r rest =>
            constructor
            · have hr : r ∈ mergeTerms xs' ys' := by rw [h]; exact List.mem_cons_self
              exact mergeTerms_bound_go _ x.monomial xs' ys' (Nat.le_refl _)
                (Sorted_head_gt_all xs' x hx)
                (fun t ht => by rw [hm_eq]; exact Sorted_head_gt_all ys' y hy t ht)
                r hr
            · rw [h] at ih_sub; exact ih_sub
      · -- x < y (lt case)
        next hlt =>
        have hgt := grevlex_flip hlt
        have ih_sub := ih (x :: xs') ys' (by simp_all; grind) hx (Sorted_tail hy)
        cases h : mergeTerms (x :: xs') ys' with
        | nil => exact True.intro
        | cons r rest =>
          constructor
          · have hr : r ∈ mergeTerms (x :: xs') ys' := by rw [h]; exact List.mem_cons_self
            exact mergeTerms_bound_go _ y.monomial (x :: xs') ys' (Nat.le_refl _)
              (fun t ht => by
                cases ht with
                | head => exact hgt
                | tail _ ht => exact grevlex_trans hgt (Sorted_head_gt_all xs' x hx t ht))
              (Sorted_head_gt_all ys' y hy)
              r hr
          · rw [h] at ih_sub; exact ih_sub

theorem sorted_mergeTerms (xs ys : List (PolyTerm R)) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mergeTerms xs ys) :=
  sorted_mergeTerms_go _ xs ys (Nat.le_refl _) hx hy

theorem sorted_add (p q : Polynomial R) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (add p q).terms := sorted_mergeTerms p.terms q.terms hp hq

theorem sorted_mul (p q : Polynomial R) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (mul p q).terms := by sorry

end Theorems

/-! ## fromGrindPoly correctness -/

section FromGrindCorrectness
variable {R : Type} [inst : Grind.CommRing R]
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast
open Grind.Semiring Grind.Ring

private theorem fromGrindPoly_go_append (p : CommRing.Poly) (acc : List (PolyTerm Int)) :
    fromGrindPoly.go p acc = acc ++ fromGrindPoly.go p [] := by
  induction p generalizing acc with
  | num k => simp only [fromGrindPoly.go]; split <;> simp
  | add k m p ih =>
    simp only [fromGrindPoly.go]; split
    · exact ih acc
    · simp only [List.nil_append]; rw [ih (acc ++ _), ih [⟨k, m⟩]]; simp

attribute [local instance] Grind.Ring.zsmul

private theorem zero_add_local (a : R) : 0 + a = a := by rw [add_comm, add_zero]

private theorem fromGrindPoly_go_denote (ctx : Context R) (p : CommRing.Poly)
    (acc : List (PolyTerm Int)) :
    denoteTerms ctx ((fromGrindPoly.go p acc).map fun t => ⟨Int.cast t.coefficient, t.monomial⟩) =
    denoteTerms ctx (acc.map fun t => ⟨Int.cast t.coefficient, t.monomial⟩) + p.denote ctx := by
  induction p generalizing acc with
  | num k =>
    simp only [fromGrindPoly.go]
    split
    · next h =>
      simp at h
      subst h
      unfold Poly.denote
      rw [intCast_zero, add_zero]
    · unfold Poly.denote
      simp only [List.map_append, List.map_cons, List.map_nil, denoteTerms_append, denoteTerms,
        Mon.denote, mul_one, add_zero]
  | add k m p ih =>
    simp only [fromGrindPoly.go]
    split
    · next h =>
      simp at h
      subst h
      rw [ih]
      congr 1
      unfold Poly.denote
      rw [zsmul_eq_intCast_mul, intCast_zero, zero_mul, add_comm (0 : R), add_zero]
      cases p with
      | num _ => rfl
      | add _ _ _ => rfl
    · rw [ih]
      simp only [List.map_append, List.map_cons, List.map_nil, denoteTerms_append, denoteTerms,
        add_zero]
      have hd : ∀ (q : Poly), Poly.denote ctx q =
          match q with
          | .num k => ↑k
          | .add k m q => k • Mon.denote ctx m + Poly.denote ctx q := by
        intro q; cases q with | num _ => rfl | add _ _ _ => rfl
      rw [hd (.add k m p)]
      simp only [zsmul_eq_intCast_mul, add_assoc]

theorem denote_fromGrindPolyAs (ctx : Context R) (p : CommRing.Poly) :
    denote ctx (fromGrindPolyAs p) = p.denote ctx := by
  simp only [fromGrindPolyAs, fromGrindPoly, denote]
  rw [fromGrindPoly_go_denote ctx p []]
  simp [denoteTerms, zero_add_local]

end FromGrindCorrectness

end Polynomial
end Macaulean
