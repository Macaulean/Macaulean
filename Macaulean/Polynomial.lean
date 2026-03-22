/-
  New polynomial representation for Macaulean.

  Polynomials as sorted lists of coefficient-monomial pairs, using
  Grind.CommRing.Mon for monomials in strictly decreasing grevlex order.
-/
import Lean
open Lean Grind CommRing
namespace Macaulean

structure Mon (n : Nat) where
  powers : Vector Nat n
  deriving Repr, Inhabited, BEq

structure PolyTerm (R : Type) (n : Nat) where
  coefficient : R
  monomial : Mon n
  deriving Repr, Inhabited, BEq

structure Polynomial (R : Type) (n : Nat) where
  terms : List (PolyTerm R n)
  deriving Repr, Inhabited, BEq

#check Nat.lt

-- Coersions to higher numbers of variables
@[coe]
def Mon.liftVars {h : n ≤ m} (mon : Mon n) : Mon m :=
  ⟨(mon.powers.rightpad m 0).cast (by simp [h])⟩
instance : Coe (Mon n) (Mon (n + k)) := ⟨Mon.liftVars (h := by simp)⟩

@[coe]
def PolyTerm.liftVars {h : n ≤ m} (p : PolyTerm R n) : PolyTerm R m :=
  ⟨p.coefficient, p.monomial.liftVars (h := h)⟩
instance : Coe (PolyTerm R n) (PolyTerm R (n+k)) :=
  ⟨PolyTerm.liftVars (h := by simp)⟩

@[coe]
def Polynomial.liftVars {h : n ≤ m} (p : Polynomial R n) : Polynomial R m :=
  ⟨p.terms.map (PolyTerm.liftVars (h := h))⟩
instance : Coe (Polynomial R n) (Polynomial R (n + k)) :=
  ⟨Polynomial.liftVars (h := by simp)⟩

--TODO tail recursion
def numVarsMon : CommRing.Mon → Nat
  | .unit => 0
  | .mult ⟨v,_⟩ m => max (v+1) (numVarsMon m)

def numVars : CommRing.Poly →  Nat
  | .num _ => 0
  | .add _ mon t =>
    max (numVarsMon mon) <| numVars t


namespace Mon

def degree (m : Mon n) : Nat := m.powers.sum

def grevlex (m1 m2 : Mon n) : Ordering :=
  let d1 := m1.degree
  let d2 := m2.degree
  (compare d1 d2).then (
    -- we `compareOfLessAndEq` this so that we can use < on lists, which has
    -- more theorems proven about it
    (compareOfLessAndEq m1.powers m2.powers).swap)

--this is the same as grevlex_swap
instance {n : Nat} : Std.OrientedCmp (grevlex (n := n)) := by
  constructor
  intro a b
  simp only [Mon.grevlex, Ordering.swap_then,
    ← Std.OrientedCmp.eq_swap]
  congr
  apply compareOfLessAndEq_eq_swap
  · exact Vector.le_antisymm
  · exact Vector.le_total
  · exact Vector.not_le

instance : Std.LawfulEqCmp (grevlex (n := n)) := by
  constructor
  intro ⟨a⟩ ⟨b⟩
  have h := (compareOfLessAndEq_eq_eq (α := Vector Nat n) (Vector.le_refl) (by simp) (x := a) (y := b))
  simp [
    Mon.grevlex,
    h,
    Ordering.then_eq_eq,
    Ordering.swap_eq_eq]

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

def denote [Grind.CommRing R] (ctx : Context R) (m : Mon n) : R :=
  (m.powers.mapIdx (fun i k => (ctx.get i ^ k))).foldl (.*.) 1

def mul (m1 m2 : Mon n) : Mon n :=
  ⟨m1.powers + m2.powers⟩

def unit : Mon n := ⟨Vector.zero⟩

def fromGrindMon (m : CommRing.Mon) : Mon (numVarsMon m) :=
  match h : m with
  | .unit => Mon.unit
  | .mult ⟨v, k⟩ m' =>
    let m'Thm : numVarsMon m' ≤ numVarsMon m := by
      simp [numVarsMon, h]
      apply Nat.le_max_right
    let vThm : v < numVarsMon m := by
      simp [numVarsMon, h]
      apply Nat.le_max_left
    let rest : Mon (numVarsMon m) :=
      Mon.liftVars (h := m'Thm) (fromGrindMon m')
    ⟨(rest.powers.set v ((rest.powers.get ⟨v, vThm⟩) + k)).cast (congrArg _ h)⟩

end Mon

namespace Polynomial

def zero {n : Nat} : Polynomial R n := ⟨[]⟩

def ofTerm (t : PolyTerm R n) : Polynomial R n := ⟨[t]⟩

abbrev Sorted {R} (l : List (PolyTerm R n)) : Prop :=
  l.Pairwise fun m₁ m₂ => m₁.monomial.grevlex m₂.monomial = .gt

--TODO prove equivalence with the Prop
def isSorted : List (PolyTerm R n) → Bool
  | [] => true
  | [_] => true
  | t₁ :: t₂ :: ts => t₁.monomial.grevlex t₂.monomial == .gt && isSorted (t₂ :: ts)

def denoteTerms [Grind.CommRing R] (ctx : Context R) : List (PolyTerm R n) → R
  | [] => 0
  | t :: ts => t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts

def denote [Grind.CommRing R] (ctx : Context R) (p : Polynomial R n) : R :=
  denoteTerms ctx p.terms

def insertTerm [Grind.CommRing R] [DecidableEq R]
    (c : R) (m : Mon n) (ts : List (PolyTerm R n)) : List (PolyTerm R n) :=
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
    (p : Polynomial R n) (c : R) (m : Mon n) : Polynomial R n :=
  ⟨insertTerm c m p.terms⟩

def mergeTerms [Grind.CommRing R] [DecidableEq R]
    (xs ys : List (PolyTerm R n)) : List (PolyTerm R n) :=
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

def add [Grind.CommRing R] [DecidableEq R] (p q : Polynomial R n) : Polynomial R n :=
  ⟨mergeTerms p.terms q.terms⟩

instance [Grind.CommRing R] [DecidableEq R] : Add (Polynomial R n) := ⟨add⟩

def smul [Grind.CommRing R] (c : R) (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun t => ⟨c * t.coefficient, t.monomial⟩⟩

def mulMon [Grind.CommRing R] (c : R) (m : Mon n) (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun t => ⟨c * t.coefficient, m.mul t.monomial⟩⟩

def mulTerms [Grind.CommRing R] [DecidableEq R]
    (ts : List (PolyTerm R n)) (q : Polynomial R n) : Polynomial R n :=
  match ts with
  | [] => zero
  | t :: rest => add (mulMon t.coefficient t.monomial q) (mulTerms rest q)

def mul [Grind.CommRing R] [DecidableEq R] (p q : Polynomial R n) : Polynomial R n :=
  mulTerms p.terms q

instance [Grind.CommRing R] [DecidableEq R] : Mul (Polynomial R n) := ⟨mul⟩

def neg [Neg R] (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun t => ⟨-t.coefficient, t.monomial⟩⟩

instance [Neg R] : Neg (Polynomial R n) := ⟨neg⟩

def sub [Grind.CommRing R] [DecidableEq R] (p q : Polynomial R n) : Polynomial R n :=
  add p (neg q)

instance [Grind.CommRing R] [DecidableEq R] : Sub (Polynomial R n) := ⟨sub⟩

def leadTerm (p : Polynomial R n) : Option (PolyTerm R n) := p.terms.head?

def tail (p : Polynomial R n) : Polynomial R n := ⟨p.terms.tail⟩

def fromGrindPoly (p : CommRing.Poly) : Polynomial Int (numVars p) :=
  ⟨go p (by simp) []⟩
where
  go (q : CommRing.Poly) (h : numVars q ≤ numVars p) (acc : List (PolyTerm Int (numVars p))) : List (PolyTerm Int (numVars p)) :=
    match h2 : q with
    | .num k => if k == 0 then acc else acc ++ [⟨k, .unit⟩]
    | .add k m p' =>
      let p'Thm : numVars p' ≤ numVars p := by
        calc
          numVars p' ≤ numVars q := by simp [h2, numVars]; apply Nat.le_max_right
          _ ≤ numVars p := by simp [h, h2]
      let monThm : numVarsMon m ≤ numVars p := by
        calc
          numVarsMon m ≤ numVars q := by
            simp [h2, numVars]
            exact Nat.le_max_left _ _
          _ ≤ numVars p := by simp [h, h2]
      let mon : Mon (numVars p) := (Mon.fromGrindMon m).liftVars (h := monThm)
      if k == 0 then go p' p'Thm acc else go p' p'Thm (acc ++ [⟨k, mon⟩])

def fromGrindPolyAs [inst : Grind.CommRing R] (p : CommRing.Poly) : Polynomial R (numVars p) :=
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
@[simp] theorem denote_mk (ctx : Context R) (ts : List (PolyTerm R n)) :
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
  | nil => simp only [insertTerm]; split
           · next h => subst h; simp [zero_mul, zero_add']
           · simp [add_zero]
  | cons t rest ih =>
    simp only [insertTerm]; split
    · split
      · next h => subst h; simp [zero_mul, zero_add']
      · simp
    · next hg => have hm : m = t.monomial := by
                    apply Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex)
                    trivial
                 split
                 · next hc => simp only [denoteTerms_cons]; rw [hm, ← add_assoc, ← right_distrib, hc, zero_mul, zero_add']
                 · simp only [denoteTerms_cons]; rw [hm, ← add_assoc, ← right_distrib]
    · simp only [denoteTerms_cons]; rw [ih, add_left_comm']

-- Add instances to let ac_nf work
instance : Std.Associative (α := R) (.*.) := ⟨mul_assoc⟩
instance : Std.Commutative (α := R) (.*.) := ⟨CommRing.mul_comm⟩

instance : Std.Associative (α := R) (.+.) := ⟨add_assoc⟩
instance : Std.Commutative (α := R) (.+.) := ⟨add_comm⟩

theorem denoteTerms_mergeTerms (ctx : Context R) (xs ys : List (PolyTerm R n)) :
    denoteTerms ctx (mergeTerms xs ys) = denoteTerms ctx xs + denoteTerms ctx ys := by
  fun_induction mergeTerms xs ys with
  | case1 =>
    simp [zero_add']
  | case2 =>
    simp [add_zero]
  | case3 x xs y ys ordHyp indHyp =>
    conv =>
      lhs
      unfold denoteTerms
      right
      apply indHyp
    simp
    ac_rfl
  | case4 x xs y ys ordHyp coeff coeffZero indHyp =>
    simp [indHyp]
    have h : x.monomial = y.monomial := Mon.eq_of_grevlex ordHyp
    rw [h]
    conv =>
      rhs
      rw [add_assoc]
      right
      rw [← add_assoc]
      left
      rw [add_comm]
    simp only [← add_assoc, ← right_distrib]
    simp only [coeff, coeffZero, zero_mul, zero_add']
  | case5 x xs y ys ordHyp c coeffHyp indHyp=>
    simp [indHyp,c,right_distrib]
    have h : x.monomial = y.monomial := Mon.eq_of_grevlex ordHyp
    rw [h]
    ac_nf
  | case6 x xs y ys ordHyp indHyp =>
    conv =>
      lhs
      unfold denoteTerms
      right
      apply indHyp
    simp
    ac_rfl

theorem denote_add (ctx : Context R) (p q : Polynomial R n) :
    denote ctx (add p q) = denote ctx p + denote ctx q :=
  denoteTerms_mergeTerms ctx p.terms q.terms

omit deceq in
theorem denoteTerms_map_smul (ctx : Context R) (c : R) (ts : List (PolyTerm R n)) :
    denoteTerms ctx (ts.map fun t => ⟨c * t.coefficient, t.monomial⟩) = c * denoteTerms ctx ts := by
  induction ts with
  | nil => simp [mul_zero]
  | cons t ts ih => simp [ih, left_distrib, mul_assoc]

omit deceq in
theorem denote_smul (ctx : Context R) (c : R) (p : Polynomial R n) :
    denote ctx (smul c p) = c * denote ctx p := by simp [smul, denote, denoteTerms_map_smul]

#check Context

-- unfortunately most of the messiness with this theorem have to do with
-- working with Vectors/Arrays
omit deceq in
theorem denote_mul_mon {ctx : Context R} {m1 m2 : Mon n}
  : (m1.mul m2).denote ctx = m1.denote ctx * m2.denote ctx := by
  simp only [Mon.mul, Mon.denote]
  --generalize out all of the important parameters
  suffices h : ∀ {off : Nat} {acc1 acc2 : R}, Vector.foldl (fun x1 x2 => x1 * x2) (acc1 * acc2)
    (Vector.mapIdx (fun i k => RArray.get ctx (i + off) ^ k) (Vector.zipWith (fun x1 x2 => x1 + x2) m1.powers m2.powers)) =
  Vector.foldl (fun x1 x2 => x1 * x2) acc1 (Vector.mapIdx (fun i k => RArray.get ctx (i + off) ^ k) m1.powers) *
    Vector.foldl (fun x1 x2 => x1 * x2) acc2 (Vector.mapIdx (fun i k => RArray.get ctx (i + off) ^ k) m2.powers) by
      replace h := h (off := 0) (acc1 := 1) (acc2 := 1)
      simp [mul_one] at h
      exact h
  intro off acc1 acc2
  have (eq := powers1) m1p := m1.powers
  have (eq := powers2) m2p := m2.powers
  rw [← powers1, ← powers2]
  clear m1 powers1 m2 powers2
  induction n generalizing off acc1 acc2
  case zero =>
    simp [
      Vector.foldl,
      Array.eq_empty_iff_size_eq_zero.mpr,
      m1p.size_toArray,m2p.size_toArray]

  case succ n ih =>
    have ⟨⟨head1 :: tail1⟩, len1⟩ := m1p
    have ⟨⟨head2 :: tail2⟩, len2⟩ := m2p
    simp at len1 len2
    simp [Vector.foldl, Vector.mapIdx, Vector.zipWith]
    replace ih := ih
      (acc1 := acc1 * (ctx.get off ^ head1))
      (acc2 := acc2 * (ctx.get off ^ head2))
      (off := 1 + off)
      (m1p := tail1.toArray.toVector.cast len1)
      (m2p := tail2.toArray.toVector.cast len2)
    simp [← add_assoc] at ih
    conv =>
      rhs
      apply (Eq.symm ih)
    congr 1
    simp [Semiring.pow_add]
    ac_nf

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
    apply denote_mul_mon


omit deceq in
theorem denote_mulMon (ctx : Context R) (c : R) (m : Mon n) (p : Polynomial R n) :
    denote ctx (mulMon c m p) = c * m.denote ctx * denote ctx p := by
  simp [mulMon, denote, denoteTerms_map_mulMon]

theorem denote_mulTerms (ctx : Context R) (ts : List (PolyTerm R n)) (q : Polynomial R n) :
    denote ctx (mulTerms ts q) = denoteTerms ctx ts * denote ctx q := by
  induction ts with
  | nil => simp [mulTerms, denote_zero, zero_mul]
  | cons t ts ih =>
    simp only [mulTerms, denote_add, denote_mulMon, denoteTerms_cons, ih]
    rw [right_distrib, mul_assoc]

theorem denote_mul (ctx : Context R) (p q : Polynomial R n) :
    denote ctx (mul p q) = denote ctx p * denote ctx q :=
  denote_mulTerms ctx p.terms q

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
  simp [denote_mul_mon]

/-! ## Grevlex ordering properties -/

omit deceq in
private theorem grevlex_swap (m₁ m₂ : Mon n) :
    (Mon.grevlex m₁ m₂).swap = Mon.grevlex m₂ m₁ := by
  simp only [Mon.grevlex, Ordering.swap_then,
    ← Std.OrientedCmp.eq_swap]
  congr
  rw [← compareOfLessAndEq_eq_swap]
  apply Vector.le_antisymm
  apply Vector.le_total
  apply Vector.not_le

omit deceq in
private theorem grevlex_flip {m₁ m₂ : Mon n} (h : m₁.grevlex m₂ = .lt) :
    m₂.grevlex m₁ = .gt := by
  have := grevlex_swap m₁ m₂; rw [h] at this; simpa using this.symm

private theorem mon_unit_mul {m : Mon n} : Mon.unit.mul m = m := by
  simp [Mon.mul, Mon.unit]
  congr
  apply (Vector.zero_add Nat.zero_add)

private theorem degree_mul {m1 m2 : Mon n} : (m1.mul m2).degree = m1.degree + m2.degree := by
  simp [Mon.mul, Mon.degree]
  simp [Vector.sum, ← Array.sum_eq_sum_toList, Vector.toList_toArray]
  conv =>
    lhs
    congr
    congr
    simp [HAdd.hAdd, Add.add]
    unfold Vector.add
  simp [Vector.toList_zipWith]
  have (eq := p1eq) ⟨⟨p1list⟩, len1⟩ := m1.powers
  have (eq := p2eq) ⟨⟨p2list⟩, len2⟩ := m2.powers
  clear p1eq p2eq
  simp at len1 len2 ⊢
  clear m1 m2
  induction n generalizing p1list p2list
  case zero =>
    have h1 : p1list = [] := List.eq_nil_of_length_eq_zero len1
    have h2 : p2list = [] := List.eq_nil_of_length_eq_zero len2
    simp [h1, h2]
  case succ n ih =>
    match p1list, p2list with
    | [], _ =>
      contradiction
    | _, [] =>
      contradiction
    | head1 :: tail1, head2 :: tail2 =>
      simp
      ac_nf
      congr
      apply ih
      --let grind do the arithmetic
      grind
      grind


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
    apply Vector.lt_iff_exists.mpr
    replace hlex := Vector.lt_iff_exists.mp hlex
    --find the i where the powers differ
    rcases hlex with ⟨i, ltn, h⟩
    exists i, ltn
    simpa [Mon.mul]

/-! ## Sortedness preservation -/

#check List.pairwise_cons

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
    split
    trivial
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
      split
      case isTrue => exact hs
      case isFalse =>
        apply pairwise_cons_trans.mpr
        exact ⟨hgt, hs⟩
    · -- m.grevlex t.monomial = .eq
      next heq =>
      have hm_eq : m = t.monomial := Mon.eq_of_grevlex heq
      subst hm_eq
      clear heq
      split
      · exact hs_rest
      · cases rest with
        | nil => apply List.pairwise_singleton
        | cons t' rest' =>
          apply pairwise_cons_trans.mpr
          constructor
          · exact (pairwise_cons_trans.mp hs).1
          · exact hs_rest
    · -- m.grevlex t.monomial = .lt
      next hlt =>
      have hgt := grevlex_flip hlt
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
  fun_induction mergeTerms xs ys
  any_goals
    simp
  case case3 x xs y ys ordHyp indHyp =>
    apply List.instTransSubset.trans
    apply indHyp
    simp
  --cases 4 and 5 are identical
  any_goals
    try next indHyp =>
      apply List.instTransSubset.trans
      apply indHyp
      apply List.subset_cons_of_subset
      simp
  case case6 x xs y ys ordHyp indHyp =>
    apply List.instTransSubset.trans
    apply indHyp
    simp
    apply List.subset_cons_of_subset
    simp

theorem sorted_mergeTerms (xs ys : List (PolyTerm R n)) (hx : Sorted xs) (hy : Sorted ys) :
    Sorted (mergeTerms xs ys) := by
  fun_induction mergeTerms
  all_goals
    have hx' := (List.pairwise_map (f := PolyTerm.monomial) (R := fun m1 m2 => m1.grevlex m2 = .gt)).mpr hx
    have hy' := (List.pairwise_map (f := PolyTerm.monomial) (R := fun m1 m2 => m1.grevlex m2 = .gt)).mpr hy
  case case1 => trivial
  case case2 => trivial
  case case3 x xs y ys ordHyp indHyp =>
    unfold Sorted
    simp
    specialize indHyp (Sorted_tail hx) hy
    constructor
    case left =>
      intros a aHyp
      have aHypMon := mergeTerms_monomials <| List.mem_map_of_mem aHyp
      replace aHypMon := List.mem_append.mp aHypMon
      simp only [List.map_cons, List.pairwise_cons] at hx' hy'
      cases aHypMon with
      | inl =>
        apply hx'.left
        trivial
      | inr h =>
        by_cases h2 : a.monomial = y.monomial
        case pos => simp [h2, ordHyp]
        case neg =>
          apply Mon.grevlex_trans ordHyp
          apply hy'.left
          simp [List.map_cons] at h
          cases h
          next h =>
            contradiction
          next h =>
            simp
            trivial
    case right =>
      trivial
  case case4 x xs y ys ordHyp coeff coeffHyp indHyp =>
    specialize indHyp (Sorted_tail hx) (Sorted_tail hy)
    exact indHyp
  case case5 x xs y ys ordHyp coeff coeffHyp indHyp =>
    simp only [List.map_cons, List.pairwise_cons] at hx' hy'
    simp [Sorted]
    specialize indHyp (Sorted_tail hx) (Sorted_tail hy)
    constructor
    case left =>
      intros a aHyp
      replace aHyp := mergeTerms_monomials <| List.mem_map_of_mem (f := PolyTerm.monomial) aHyp
      simp only [List.mem_append] at aHyp
      replace ordHyp := Mon.eq_of_grevlex ordHyp
      cases aHyp with
      | inl =>
        apply hx'.left
        trivial
      | inr h =>
        simp [ordHyp]
        apply hy'.left
        trivial
    case right =>
      trivial
  case case6 x xs y ys ordHyp indHyp =>
    simp only [List.map_cons, List.pairwise_cons] at hx' hy'
    simp [Sorted]
    specialize indHyp hx (Sorted_tail hy)
    constructor
    case left =>
      intros a aHyp
      replace ordHyp := grevlex_flip ordHyp
      replace aHyp := mergeTerms_monomials <| List.mem_map_of_mem (f := PolyTerm.monomial) aHyp
      simp only [List.mem_append] at aHyp
      cases aHyp with
      | inl h =>
        by_cases h2 : a.monomial = x.monomial
        case pos => simp [h2, ordHyp]
        case neg =>
          apply Mon.grevlex_trans ordHyp
          apply hx'.left
          simp at h
          cases h
          next h =>
            contradiction
          next h =>
            simp
            trivial
      | inr h =>
        apply hy'.left
        trivial
    case right =>
      trivial

theorem sorted_add (p q : Polynomial R n) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (add p q).terms := sorted_mergeTerms p.terms q.terms hp hq

theorem sorted_mul (p q : Polynomial R n) (hp : Sorted p.terms) (hq : Sorted q.terms) :
    Sorted (mul p q).terms := by
  unfold mul
  fun_induction mulTerms p.terms q
  case case1 =>
    unfold zero
    simp [Sorted]
  case case2 t ts indHyp =>
    apply sorted_add
    case hp =>
      unfold mulMon
      simp [Sorted]
      apply List.Pairwise.map
      simp
      intro a b ineq
      apply grevlex_mul_mono
      apply ineq
      apply hq
    case hq => exact indHyp


end Theorems

/-! ## fromGrindPoly correctness -/

section FromGrindCorrectness
variable {R : Type} [inst : Grind.CommRing R]
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast
open Grind.Semiring Grind.Ring

--TODO reconsider the theorems in this section

-- private theorem fromGrindPoly_go_append (p : CommRing.Poly) (acc : List (PolyTerm Int (numVars p))) :
--     fromGrindPoly.go p acc = acc ++ fromGrindPoly.go p [] := by
--   induction p generalizing acc with
--   | num k => simp only [fromGrindPoly.go]; split <;> simp
--   | add k m p ih =>
--     simp only [fromGrindPoly.go]; split
--     · exact ih acc
--     · simp only [List.nil_append]; rw [ih (acc ++ _), ih [⟨k, m⟩]]; simp

-- attribute [local instance] Grind.Ring.zsmul

-- private theorem fromGrindPoly_go_denote (ctx : Context R) (p : CommRing.Poly)
--     (acc : List (PolyTerm Int (numVars p))) :
--     denoteTerms ctx ((fromGrindPoly.go p acc).map fun t => ⟨Int.cast t.coefficient, t.monomial⟩) =
--     denoteTerms ctx (acc.map fun t => ⟨Int.cast t.coefficient, t.monomial⟩) + p.denote ctx := by
--   induction p with
--   | num k =>
--     simp only [fromGrindPoly.go]
--     split
--     · next h =>
--       simp at h
--       subst h
--       unfold Poly.denote
--       rw [intCast_zero, add_zero]
--     · unfold Poly.denote
--       simp only [List.map_append, List.map_cons, List.map_nil, denoteTerms_append, denoteTerms,
--         Mon.denote, mul_one, add_zero]
--   | add k m p ih =>
--     simp only [fromGrindPoly.go]
--     split
--     · next h =>
--       simp at h
--       subst h
--       rw [ih]
--       congr 1
--       unfold Poly.denote
--       rw [zsmul_eq_intCast_mul, intCast_zero, zero_mul, add_comm (0 : R), add_zero]
--       cases p with
--       | num _ => rfl
--       | add _ _ _ => rfl
--     · rw [ih]
--       simp only [List.map_append, List.map_cons, List.map_nil, denoteTerms_append, denoteTerms,
--         add_zero]
--       have hd : ∀ (q : Poly), Poly.denote ctx q =
--           match q with
--           | .num k => ↑k
--           | .add k m q => k • Mon.denote ctx m + Poly.denote ctx q := by
--         intro q; cases q with | num _ => rfl | add _ _ _ => rfl
--       rw [hd (.add k m p)]
--       simp only [zsmul_eq_intCast_mul, add_assoc]

-- theorem denote_fromGrindPolyAs (ctx : Context R) (p : CommRing.Poly) :
--     denote ctx (fromGrindPolyAs p) = p.denote ctx := by
--   simp only [fromGrindPolyAs, fromGrindPoly, denote]
--   rw [fromGrindPoly_go_denote ctx p []]
--   simp [zero_add']

end FromGrindCorrectness

end Polynomial
end Macaulean
