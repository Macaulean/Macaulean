/-
  New polynomial representation for Macaulean.

  Polynomials as sorted lists of coefficient-monomial pairs, using
  Vector Nat n for monomials.
-/
import Lean
import MRDI
open Lean Grind CommRing
namespace Macaulean

-- TODO we should probably replicate what Vector Nat n does and
-- store the hypotheses that the length of powers
structure Mon (n : Nat) where
  powers : List Nat -- Vector Nat n
  powers_length : powers.length = n
  deriving Repr, BEq

instance : Inhabited (Mon n) := ⟨List.replicate n 0, by simp⟩

structure PolyTerm (R : Type) (n : Nat) where
  coefficient : R
  monomial : Mon n
  deriving Repr, Inhabited, BEq

structure Polynomial (R : Type) (n : Nat) where
  terms : List (PolyTerm R n)
  deriving Repr, Inhabited, BEq

namespace Polynomial
inductive Expr (R : Type) (n : Nat) where
  | sum (terms : List (Expr R n))
  | product (factors : List (Expr R n))
  | pow (p : Expr R n) (n : Nat)
  | term (term : PolyTerm R n)

instance [MrdiType R] : MrdiType (Polynomial R n) := sorry
instance [MrdiType R] : MrdiType (Polynomial.Expr R n) := sorry

end Polynomial

-- Coersions to higher numbers of variables
@[coe]
def Mon.liftVars {h : n ≤ m} (mon : Mon n) : Mon m :=
  ⟨mon.powers.rightpad m 0, by simp [mon.powers_length,h]⟩
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

/-
Basic declarations for monomials
-/
namespace Mon

def ofPowers (powers : List Nat) : Mon powers.length := ⟨powers,rfl⟩

def degree (m : Mon n) : Nat := m.powers.sum

def grevlex (m1 m2 : Mon n) : Ordering :=
  let d1 := m1.degree
  let d2 := m2.degree
  (compare d1 d2).then (
    -- we `compareOfLessAndEq` this so that we can use < on lists, which has
    -- more theorems proven about it
    (compareOfLessAndEq m1.powers m2.powers).swap)

def Grevlex (m1 m2 : Mon n) : Prop := m1.grevlex m2 = .gt

/--
  Grevlex is decidable
-/
instance : @DecidableRel (Mon n) (Mon n) Grevlex :=
  fun m1 m2 => match h : grevlex m1 m2 with
  | .gt => .isTrue h
  | .eq => .isFalse (by simp [Grevlex, h])
  | .lt => .isFalse (by simp [Grevlex, h])

/--
  Equality is decidable for monomials
-/
instance : DecidableEq (Mon n) :=
  fun ⟨p1,_⟩ ⟨p2,_⟩ =>
    let d := (inferInstance : DecidableEq _) p1 p2
    match d with
    | .isTrue h => .isTrue (by simp [h])
    | .isFalse h => .isFalse (by simp [h])

--this is the same as grevlex_swap
instance {n : Nat} : Std.OrientedCmp (grevlex (n := n)) := by
  constructor
  intro a b
  simp only [Mon.grevlex, Ordering.swap_then,
    ← Std.OrientedCmp.eq_swap]
  congr
  apply compareOfLessAndEq_eq_swap
  · exact List.le_antisymm
  · exact List.le_total
  · exact List.not_le

instance : Std.LawfulEqCmp (grevlex (n := n)) := by
  constructor
  intro ⟨a,_⟩ ⟨b,_⟩
  have h := (compareOfLessAndEq_eq_eq (List.le_refl) (by simp) (x := a) (y := b))
  simp [
    Mon.grevlex,
    h,
    Ordering.then_eq_eq,
    Ordering.swap_eq_eq]

/--
  Denotation for monomials, `ctx` provides the substitutions for the variables
-/
def denote [Grind.CommRing R] (ctx : Context R) (m : Mon n) : R :=
  (m.powers.mapIdx (fun i k => (ctx.get i ^ k))).foldl (.*.) 1

def mul (m1 m2 : Mon n) : Mon n :=
  ⟨m1.powers.zipWith (· + ·) m2.powers,
  by simp [m1.powers_length, m2.powers_length]⟩

@[reducible]
def fromVarPower (i : Fin n) (k : Nat) : Mon n :=
  ⟨List.ofFn (fun j => if j == i then k else 0), by simp⟩

@[reducible]
def fromVar (i : Fin n) : Mon n := fromVarPower i 1

def mulVarPower (i : Fin n) (k : Nat) (m : Mon n) : Mon n :=
  (fromVarPower i k).mul m

def unit : Mon n := ⟨List.replicate n 0, by simp⟩

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
    (rest.mulVarPower ⟨v,vThm⟩ k).liftVars (h := by simp [h])
--    ⟨(rest.powers.set v ((rest.powers.get ⟨v, vThm⟩) + k)).cast (congrArg _ h)⟩

end Mon

namespace Polynomial

def zero {n : Nat} : Polynomial R n := ⟨[]⟩

def ofTerm (t : PolyTerm R n) : Polynomial R n := ⟨[t]⟩

def ofVar [One R] (i : Fin n) : Polynomial R n := ofTerm ⟨1, Mon.fromVar i⟩

abbrev Sorted {R} (l : List (PolyTerm R n)) : Prop :=
  l.Pairwise fun m₁ m₂ => m₁.monomial.grevlex m₂.monomial = .gt

--TODO prove equivalence with the Prop
def isSorted : List (PolyTerm R n) → Bool
  | [] => true
  | [_] => true
  | t₁ :: t₂ :: ts => t₁.monomial.grevlex t₂.monomial == .gt && isSorted (t₂ :: ts)

def removeZeros [Zero R] [BEq R] (p : List (PolyTerm R n)) : List (PolyTerm R n) :=
  p.filter (fun ⟨c, _⟩ => c != 0)

abbrev Normalized [Semiring R] (p : Polynomial R n) : Prop :=
  Sorted p.terms ∧ (∀ t ∈ p.terms, t.coefficient ≠ 0)

def denoteTerms [Grind.CommRing R] (ctx : Context R) : List (PolyTerm R n) → R
  | [] => 0
  | t :: ts => t.coefficient * t.monomial.denote ctx + denoteTerms ctx ts

def denote [Grind.CommRing R] (ctx : Context R) (p : Polynomial R n) : R :=
  denoteTerms ctx p.terms

def Expr.denote [CommRing R] (ctx : Context R) : Polynomial.Expr R n → R
  | .sum terms => (terms.map (Expr.denote ctx)).sum
  | .product factors => (factors.map (Expr.denote ctx)).foldl (. * .) 1
  | .pow a n => (a.denote ctx) ^ n
  | .term ⟨c,m⟩ => c * m.denote ctx

def insertTerm [Grind.CommRing R]
    (c : R) (m : Mon n) (ts : List (PolyTerm R n)) : List (PolyTerm R n) :=
  match ts with
  | [] => [⟨c, m⟩]
  | t :: rest =>
    match m.grevlex t.monomial with
    | .gt => ⟨c, m⟩ :: ts
    | .eq =>
      let c' := c + t.coefficient
      ⟨c', m⟩ :: rest
    | .lt => t :: insertTerm c m rest

/-
Addition helpers
-/
def addTerm [Grind.CommRing R]
    (p : Polynomial R n) (c : R) (m : Mon n) : Polynomial R n :=
  ⟨insertTerm c m p.terms⟩

@[reducible]
def mergeTerms [Grind.CommRing R]
    (xs ys : List (PolyTerm R n))
 : List (PolyTerm R n) :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', _ =>
    takeTillGE x ys (mergeTerms xs')
  where
    @[reducible]
    takeTillGE (x : PolyTerm R n) (ts : List (PolyTerm R n))
      (tailFunc : List (PolyTerm R n) → List (PolyTerm R n))
      : (List (PolyTerm R n)) :=
      match ts with
      | [] => x :: tailFunc []
      | t :: ts' =>
        match x.monomial.grevlex t.monomial with
        | .gt => x :: tailFunc ts
        | .eq =>
          let c := x.coefficient + t.coefficient
          ⟨c, x.monomial⟩ :: tailFunc ts'
        | .lt => t :: (takeTillGE x ts' tailFunc)

def add [Grind.CommRing R] [BEq R] (p q : Polynomial R n) : Polynomial R n :=
  ⟨removeZeros <| mergeTerms p.terms q.terms⟩

instance [Grind.CommRing R] [BEq R] : Add (Polynomial R n) := ⟨add⟩

/-
Negation and subtraction
-/
def neg [Neg R] (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun t => ⟨-t.coefficient, t.monomial⟩⟩

instance [Neg R] : Neg (Polynomial R n) := ⟨neg⟩

def sub [Grind.CommRing R] [BEq R] (p q : Polynomial R n) : Polynomial R n :=
  add p (neg q)

instance [Grind.CommRing R] [BEq R] : Sub (Polynomial R n) := ⟨sub⟩

/-
  Multiplication implementation
-/
def smul [Grind.CommRing R] (c : R) (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun ⟨c',m⟩ => ⟨c * c', m⟩⟩

def mulMon [Grind.CommRing R] (c : R) (m : Mon n) (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun ⟨c',m'⟩ => ⟨c * c', m.mul m'⟩⟩

def mulMonTerms [Grind.CommRing R] (c : R) (m : Mon n) (p : List (PolyTerm R n))
  : List (PolyTerm R n) :=
  p.map fun ⟨c',m'⟩ => ⟨c * c', m.mul m'⟩

@[reducible]
def mulTerms [Grind.CommRing R]
    (xs ys : List (PolyTerm R n)) : List (PolyTerm R n) :=
  match xs with
  | [] => []
  | ⟨c, m⟩ :: xs' =>
    --this match is a bit pointless, but it changes how things simplify
    match ys with
    | [] => []
    --we write the more complicated thing here, in exchange, lead terms is easier
    | ⟨c', m'⟩ :: ys' =>
      ⟨c * c', m.mul m'⟩ ::
      mergeTerms (mulMonTerms c m ys') (mulTerms xs' ys)

def mul [Grind.CommRing R] [BEq R] (p q : Polynomial R n) : Polynomial R n :=
  ⟨removeZeros <| mulTerms p.terms q.terms⟩

instance [Grind.CommRing R] [BEq R] : Mul (Polynomial R n) := ⟨mul⟩

/--
  Get the lead term of the polynomial,
  this does not check if the polynomial is sorted.
-/
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

end Polynomial

end Macaulean
