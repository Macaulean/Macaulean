/-
  New polynomial representation for Macaulean.

  Polynomials as sorted lists of coefficient-monomial pairs, using
  Vector Nat n for monomials.
-/
import Lean
import MRDI
import Macaulean.Polynomial.Key
open Lean Grind CommRing
namespace Macaulean

/--
A monomial in `n` variables: the exponent vector packed into a single `Nat`.

The digits of `key`, in base `Mon.base n`, are the partial sums of the
exponents, most significant digit first the total degree
(`Macaulean/Polynomial/Key.lean`).  So multiplying monomials is one `Nat.add`
and comparing them in grevlex order is one `Nat.blt` -- which is the whole
point: the kernel spends its time in `mergeTerms`, comparing monomials.

`Mon.powers` reads the exponent vector back out.  It is a faithful inverse of
the packing exactly on `Mon.WF` monomials, i.e. while the total degree stays
below `Mon.base n`; the reflective checker verifies that with `Nat.blt` before
using a product (`Polynomial.mulOk`).
-/
structure Mon (n : Nat) where
  key : Nat
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

instance : ToExpr (Mon n) where
  toExpr m := mkApp2 (.const ``Mon.mk []) (toExpr n) (toExpr m.key)
  toTypeExpr := mkApp (.const ``Mon []) <| toExpr n

instance : Inhabited (Mon n) := ⟨⟨0⟩⟩

/-- The exponent vector this key stands for. -/
def Mon.powers (m : Mon n) : List Nat := Mon.decodeKey (Mon.base n) n m.key

@[simp] theorem Mon.powers_length (m : Mon n) : m.powers.length = n := by
  simp [Mon.powers]

/-- Pack an exponent vector into a monomial in `n` variables. -/
def Mon.ofPowersN (n : Nat) (p : List Nat) : Mon n := ⟨Mon.encodeKey (Mon.base n) p⟩

def Mon.ofPowers (p : List Nat) : Mon p.length := Mon.ofPowersN p.length p

@[simp] theorem Mon.key_eq_iff_eq {m1 m2 : Mon n} : m1.key = m2.key ↔ m1 = m2 := by
  cases m1; cases m2; simp

structure PolyTerm (R : Type) (n : Nat) where
  coefficient : R
  monomial : Mon n
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, ToExpr

structure Polynomial (R : Type) (n : Nat) where
  terms : List (PolyTerm R n)
  deriving Repr, Inhabited, BEq, ReflBEq, LawfulBEq, ToExpr

namespace Polynomial
inductive Expr (R : Type) (n : Nat) where
  | sum (terms : List (Expr R n))
  | product (factors : List (Expr R n))
  | pow (p : Expr R n) (n : Nat)
  | term (term : PolyTerm R n)


end Polynomial

-- Coersions to higher numbers of variables
set_option linter.unusedVariables false in
@[coe]
def Mon.liftVars {h : n ≤ m} (mon : Mon n) : Mon m :=
  Mon.ofPowersN m (mon.powers.rightpad m 0)
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

/--
A monomial is *well formed* when its key really is the packing of its own
exponent vector, and its total degree is below the digit base.

Packing is faithful exactly on well-formed monomials: `Mon.powers` inverts
`Mon.ofPowersN` there, `Mon.mul` (a key addition) agrees with adding exponent
vectors there, and `Mon.grevlex` (a key comparison) is the classical grevlex
order there.  Nothing here is a soundness assumption: the reflective checker
computes `Mon.wf` and the degree bound with the kernel before it uses a
product (`Polynomial.mulOk`).
-/
def WF (m : Mon n) : Prop :=
  m.powers.sum < base n ∧ m.key = encodeKey (base n) m.powers

/--
Decidable form of `Mon.WF`: one walk down the digits of the key, checking that
they are non-decreasing and that there are no more than `n` of them.

Deliberately *not* `decide (m.powers.sum < base n) && m.key == encodeKey …`:
that decodes the key into a list, sums the list and re-encodes it, three walks
and two list allocations, and the reflective checker runs it on every factor of
every product.  `Mon.wf_iff` says the two agree.
-/
def wf (m : Mon n) : Bool := wfFrom (base n) n 0 m.key

/-- The total degree, read off the same digit walk as `Mon.wf` -- the last
digit of a packed key is its total degree.  Agrees with `Mon.degree` on
well-formed monomials (`Mon.degree_eq_degB`), which is where it is used. -/
def degB (m : Mon n) : Nat := topFrom (base n) n 0 m.key

theorem wf_iff {m : Mon n} : m.wf = true ↔ m.WF := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hs := sum_decodeFrom_eq_topFrom (base n) n 0 m.key h
      have hlt := topFrom_lt (base n) (base_pos n) n 0 m.key (base_pos n)
      show (decodeFrom (base n) n 0 m.key).sum < base n
      omega
    · exact (encodeFrom_decodeFrom (base n) (base_pos n) n 0 m.key h).symm
  · intro ⟨hsum, hkey⟩
    show wfFrom (base n) n 0 m.key = true
    rw [hkey]
    exact wfFrom_encodeFrom (base n) (base_pos n) m.powers n 0 (by simp) (by omega)

theorem powers_ofPowersN {p : List Nat} (hlen : p.length = n) (hsum : p.sum < base n) :
    (ofPowersN n p).powers = p :=
  decodeKey_encodeKey _ (base_pos n) p n hlen hsum

theorem wf_ofPowersN {p : List Nat} (hlen : p.length = n) (hsum : p.sum < base n) :
    (ofPowersN n p).WF := by
  refine ⟨?_, ?_⟩ <;> rw [powers_ofPowersN hlen hsum]
  · exact hsum
  · rfl

def degree (m : Mon n) : Nat := m.powers.sum

/-- On a well-formed monomial the cheap degree is the degree. -/
theorem degree_eq_degB {m : Mon n} (h : m.wf = true) : m.degree = m.degB := by
  have := sum_decodeFrom_eq_topFrom (base n) n 0 m.key h
  show (decodeFrom (base n) n 0 m.key).sum = topFrom (base n) n 0 m.key
  omega

/-! ### The order -/

/--
Grevlex, as a single comparison of the packed keys.

Spelled with `Nat.beq`/`Nat.ble` and `cond` rather than `compare`: `compare`
goes through `Decidable` instances, so in the kernel every monomial comparison
would build -- and the whnf cache would then retain -- a `Nat.le` proof term.
`mergeTerms` does essentially nothing but compare monomials, so this is the
hot path.  `Mon.grevlex_eq_compare` says the two agree.
-/
def grevlex (m1 m2 : Mon n) : Ordering :=
  bif Nat.beq m1.key m2.key then .eq
  else bif Nat.ble m1.key m2.key then .lt else .gt

private theorem beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr (fun hh => absurd (Nat.eq_of_beq_eq_true hh) h)

private theorem ble_eq_false_of_lt {a b : Nat} (h : b < a) : Nat.ble a b = false :=
  Bool.eq_false_iff.mpr (fun hh => absurd (Nat.le_of_ble_eq_true hh) (by omega))

theorem grevlex_eq_compare (m1 m2 : Mon n) : m1.grevlex m2 = compare m1.key m2.key := by
  show (bif Nat.beq m1.key m2.key then Ordering.eq
        else bif Nat.ble m1.key m2.key then Ordering.lt else Ordering.gt) = _
  rcases Nat.lt_trichotomy m1.key m2.key with h | h | h
  · rw [beq_eq_false_of_ne (by omega), Nat.ble_eq_true_of_le (Nat.le_of_lt h)]
    exact (Nat.compare_eq_lt.mpr h).symm
  · rw [h, Nat.beq_refl]
    exact (Nat.compare_eq_eq.mpr rfl).symm
  · rw [beq_eq_false_of_ne (by omega), ble_eq_false_of_lt h]
    exact (Nat.compare_eq_gt.mpr h).symm

def Grevlex (m1 m2 : Mon n) : Prop := m2.key < m1.key

/-- The classical definition of grevlex, on exponent vectors: total degree
first, then reverse-lexicographic with the swap. -/
def grevlexSpec (m1 m2 : Mon n) : Ordering :=
  (compare m1.degree m2.degree).then ((compare m1.powers.reverse m2.powers.reverse).swap)

/-- **The order is unchanged.**  Comparing packed keys agrees with the
classical grevlex comparison of exponent vectors, on well-formed monomials. -/
theorem grevlex_eq_grevlexSpec {m1 m2 : Mon n} (h1 : m1.WF) (h2 : m2.WF) :
    m1.grevlex m2 = m1.grevlexSpec m2 := by
  obtain ⟨hs1, hk1⟩ := h1
  obtain ⟨hs2, hk2⟩ := h2
  rw [grevlex_eq_compare, grevlexSpec, hk1, hk2, degree, degree]
  exact compare_encodeKey (base n) _ _ (by simp) hs1 hs2

theorem grevlex_iff_grevlex_gt {m1 m2 : Mon n} : Grevlex m1 m2 ↔ grevlex m1 m2 = .gt := by
  simp [Grevlex, grevlex_eq_compare, Nat.compare_eq_gt]

theorem grevlex_or_eq_iff_grevlex_ge {m1 m2 : Mon n} :
    (Grevlex m1 m2 ∨ m1 = m2) ↔ (grevlex m1 m2).isGE = true := by
  constructor
  · rintro (h | rfl)
    · rw [grevlex_eq_compare, Nat.compare_eq_gt.mpr h]; rfl
    · rw [grevlex_eq_compare, Nat.compare_eq_eq.mpr rfl]; rfl
  · intro h
    rcases hc : compare m1.key m2.key with _ | _ | _
    · rw [grevlex_eq_compare, hc] at h; exact absurd h (by simp)
    · exact .inr (key_eq_iff_eq.mp (Nat.compare_eq_eq.mp hc))
    · exact .inl (Nat.compare_eq_gt.mp hc)

/--
  Grevlex is decidable
-/
instance : @DecidableRel (Mon n) (Mon n) Grevlex :=
  fun m1 m2 => inferInstanceAs (Decidable (m2.key < m1.key))

/--
  Grevlex is asymmetric
-/
instance : @Std.Asymm (Mon n) Grevlex where
  asymm _a _b abh := by simp only [Grevlex] at *; omega

/--
  Grevlex is irreflexive
-/
instance : @Std.Irrefl (Mon n) Grevlex where
  irrefl a := by simp [Grevlex]

/--
  Grevlex is trichotomous
-/
instance : @Std.Trichotomous (Mon n) Grevlex where
  trichotomous a b abh bah := by
    simp only [Grevlex, Nat.not_lt] at abh bah
    exact key_eq_iff_eq.mp (by omega)

deriving instance DecidableEq for PolyTerm, Polynomial

instance {n : Nat} : Std.OrientedCmp (grevlex (n := n)) where
  eq_swap := by
    intro a b
    simp only [grevlex_eq_compare]
    exact Std.OrientedCmp.eq_swap

instance : Std.LawfulEqCmp (grevlex (n := n)) where
  eq_of_compare {a b} h :=
    key_eq_iff_eq.mp (Nat.compare_eq_eq.mp (by rwa [grevlex_eq_compare] at h))

instance : @Trans (Mon n) _ _ Grevlex Grevlex Grevlex where
  trans hab hbc := by simp only [Grevlex] at *; omega

/-! ### Operations -/

/--
  Denotation for monomials, `ctx` provides the substitutions for the variables
-/
def denote [Grind.CommRing R] (ctx : Context R) (m : Mon n) : R :=
  (m.powers.mapFinIdx (fun i k _ => (ctx.get i ^ k))).foldl (.*.) 1

/-- Multiplying monomials is adding keys: one kernel `Nat.add`.  Faithful while
the degrees stay below `Mon.base n` (`Mon.denote_mul`). -/
def mul (m1 m2 : Mon n) : Mon n := ⟨m1.key + m2.key⟩

@[simp] theorem mul_key (m1 m2 : Mon n) : (m1.mul m2).key = m1.key + m2.key := rfl

/-- Raising a monomial to a power scales every partial sum, hence the key. -/
def pow (m : Mon n) (a : Nat) : Mon n := ⟨a * m.key⟩

@[reducible]
def fromVarPower (i : Fin n) (k : Nat) : Mon n :=
  ofPowersN n (List.ofFn (fun j => if j == i then k else 0))

@[reducible]
def fromVar (i : Fin n) : Mon n := fromVarPower i 1

def mulVarPower (i : Fin n) (k : Nat) (m : Mon n) : Mon n :=
  (fromVarPower i k).mul m

def unit : Mon n := ⟨0⟩

@[simp] theorem unit_key : (unit : Mon n).key = 0 := rfl

theorem powers_unit : (unit : Mon n).powers = List.replicate n 0 :=
  decodeFrom_zero_key (base n) n

theorem wf_unit : (unit : Mon n).WF := by
  refine ⟨?_, ?_⟩ <;> simp [powers_unit, encodeKey_replicate_zero, base_pos n]

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

end Mon

namespace Polynomial

def zero {n : Nat} : Polynomial R n := ⟨[]⟩

def ofTerm (t : PolyTerm R n) : Polynomial R n := ⟨[t]⟩

def ofVar [One R] (i : Fin n) : Polynomial R n := ofTerm ⟨1, Mon.fromVar i⟩

def ofMon [One R] (m : Mon n) : Polynomial R n := ofTerm ⟨1, m⟩

def ofConst (c : R) : Polynomial R n := ⟨[⟨c, .unit⟩]⟩

instance [OfNat R m] : OfNat (Polynomial R n) m where
  ofNat := ⟨[⟨OfNat.ofNat m, .unit⟩]⟩

def Sorted {R} (l : List (PolyTerm R n)) : Prop :=
  l.Pairwise fun m₁ m₂ => m₁.monomial.Grevlex m₂.monomial

--TODO prove equivalence with the Prop
def isSorted : List (PolyTerm R n) → Bool
  | [] => true
  | [_] => true
  | t₁ :: t₂ :: ts => t₁.monomial.grevlex t₂.monomial == .gt && isSorted (t₂ :: ts)

def sortTerms : List (PolyTerm R n) → List (PolyTerm R n) :=
  List.mergeSort (le := fun a b => (a.monomial.grevlex b.monomial).isGE)

def coalesceTerms [CommRing R] (terms : List (PolyTerm R n)) : List (PolyTerm R n) :=
  match terms with
  | [] => []
  | t :: ts => step t ts
  where
    step currTerm terms :=
      match terms with
      | [] => [currTerm]
      | t :: ts =>
        if currTerm.monomial = t.monomial
        then step ⟨currTerm.coefficient + t.coefficient, currTerm.monomial⟩ ts
        else currTerm :: step t ts

def removeZeros [Zero R] [BEq R] (p : List (PolyTerm R n)) : List (PolyTerm R n) :=
  p.filter (fun ⟨c, _⟩ => c != 0)

abbrev Normalized [Semiring R] (p : Polynomial R n) : Prop :=
  Sorted p.terms ∧ (∀ t ∈ p.terms, t.coefficient ≠ 0)

def normalize [CommRing R] [BEq R] (p : Polynomial R n) : Polynomial R n :=
  ⟨removeZeros <| coalesceTerms <| sortTerms p.terms⟩

def Equiv [CommRing R] [BEq R] (p q : Polynomial R n) : Prop := normalize p = normalize q

instance [CommRing R] [BEq R] : HasEquiv (Polynomial R n) where
  Equiv := Equiv

instance [CommRing R] [BEq R] [LawfulBEq R] : DecidableRel (@Equiv R n _ _) :=
  fun p q =>
    decidable_of_bool _ <| by
      unfold Equiv
      constructor
      case mp =>
        apply LawfulBEq.eq_of_beq
      case mpr =>
        simp

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

def termsSupport : List (PolyTerm R n) → List (Mon n) := List.map PolyTerm.monomial

def support (p : Polynomial R n) : List (Mon n) := termsSupport p.terms

def insertTerm [Grind.CommRing R]
    (term : PolyTerm R n) (ts : List (PolyTerm R n)) : List (PolyTerm R n) :=
  match ts with
  | [] => [term]
  | t :: rest =>
    match term.monomial.grevlex t.monomial with
    | .gt => term :: ts
    | .eq =>
      let c' := term.coefficient + t.coefficient
      ⟨c', term.monomial⟩ :: rest
    | .lt => t :: insertTerm term rest

/-
Addition helpers
-/
def addTerm [Grind.CommRing R]
   (q : PolyTerm R n) (p : Polynomial R n) : Polynomial R n :=
  ⟨insertTerm q p.terms⟩

/--
Reference merge of two grevlex-descending term lists, adding coefficients on
equal monomials.

This is the mathematical specification only: Lean compiles it with
`WellFounded.fix`, which the *kernel* cannot unfold, so `decide +kernel` gets
stuck on it.  `mergeTerms` below is the kernel-evaluable version; everything
downstream uses that one, and `mergeTerms_eq_spec` says the two agree.
-/
def mergeTermsSpec [Grind.CommRing R]
    (xs ys : List (PolyTerm R n))
 : List (PolyTerm R n) :=
  match xs with
  | [] => ys
  | x :: xs' =>
    takeTillGE x xs' ys
  where
    takeTillGE (x : PolyTerm R n) (xs ys: List (PolyTerm R n))
      : (List (PolyTerm R n)) :=
      match ys with
      | [] => x :: xs
      | t :: ts' =>
        match x.monomial.grevlex t.monomial with
        | .gt => x :: mergeTermsSpec xs ys
        | .eq =>
          let c := x.coefficient + t.coefficient
          ⟨c, x.monomial⟩ :: mergeTermsSpec xs ts'
        | .lt => t :: (takeTillGE x xs ts')

/-- Recursion budget for `mergeTermsF`.  Fuel only bounds the recursion depth
actually taken, so a huge literal costs nothing (the kernel decrements a `Nat`
literal, which is a GMP subtraction, not a unary step). -/
def mergeFuel : Nat := 1000000000

/--
Fuel-indexed merge: the same function as `mergeTermsSpec`, but structurally
recursive, hence unfoldable by the kernel (which is what `decide +kernel`
needs).

The fuel-0 fallback is `mergeTermsSpec` itself, so `mergeTermsF f = mergeTermsSpec`
for *every* `f` and no lemma downstream carries a fuel side-condition.  With
`mergeFuel` the fallback is unreachable in practice; if it were ever reached the
kernel would simply get stuck (a tactic failure, never an unsound proof).

The comparison is written out as `Nat.beq`/`Nat.ble` on the keys rather than as
a `match` on `Mon.grevlex`: the two agree (`mergeTermsF_cons_cons`), but the
`match` makes the kernel build an `Ordering` value and case on it at every step,
and the merge does nothing else.  On the certificate benchmarks
(`MacauleanTest/AlgebraNormPerf.lean`) that round trip is 5-7% of the whole
check.
-/
def mergeTermsF [Grind.CommRing R] :
    Nat → List (PolyTerm R n) → List (PolyTerm R n) → List (PolyTerm R n)
  | 0, xs, ys => mergeTermsSpec xs ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | fuel + 1, x :: xs, y :: ys =>
    bif Nat.beq x.monomial.key y.monomial.key then
      ⟨x.coefficient + y.coefficient, x.monomial⟩ :: mergeTermsF fuel xs ys
    else bif Nat.ble x.monomial.key y.monomial.key then
      y :: mergeTermsF fuel (x :: xs) ys
    else
      x :: mergeTermsF fuel xs (y :: ys)

/-- Merge two grevlex-descending term lists, coalescing equal monomials. -/
def mergeTerms [Grind.CommRing R]
    (xs ys : List (PolyTerm R n)) : List (PolyTerm R n) :=
  mergeTermsF mergeFuel xs ys

/--
Addition: merge the two grevlex-descending term lists, coalescing equal
monomials.

Deliberately *not* followed by `removeZeros`.  Cancellation does leave zero
coefficients behind, but stripping them after every operation costs a full
traversal of the accumulated polynomial per step, which on a left-nested sum of
`m` monomials is a second `O(m²)` on top of the merge -- about a quarter of the
whole reflective check at certificate sizes.  Stripping once at the end is
enough: `removeZeros` of a sorted list is still sorted, and two sorted lists
with the same nonzero terms become equal, which is what `checkPolyEq` compares.
-/
@[simp]
def add [Grind.CommRing R] (p q : Polynomial R n) : Polynomial R n :=
  ⟨mergeTerms p.terms q.terms⟩

instance [Grind.CommRing R] : Add (Polynomial R n) := ⟨add⟩

/-
Negation and subtraction
-/
def neg [Neg R] (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun t => ⟨-t.coefficient, t.monomial⟩⟩

instance [Neg R] : Neg (Polynomial R n) := ⟨neg⟩

def sub [Grind.CommRing R] (p q : Polynomial R n) : Polynomial R n :=
  add p (neg q)

instance [Grind.CommRing R] : Sub (Polynomial R n) := ⟨sub⟩

/-
  Multiplication implementation
-/
def smul [CommRing R] (c : R) (p : Polynomial R n) : Polynomial R n :=
  ⟨p.terms.map fun ⟨c',m⟩ => ⟨c * c', m⟩⟩

def mulMonTerms [CommRing R] (c : R) (m : Mon n) (p : List (PolyTerm R n))
  : List (PolyTerm R n) :=
  p.map fun ⟨c',m'⟩ => ⟨c * c', m.mul m'⟩

def mulMon [CommRing R] (c : R) (m : Mon n) (p : Polynomial R n) : Polynomial R n :=
  ⟨mulMonTerms c m p.terms⟩

def mulTerms [CommRing R]
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

/-- Multiplication.  Like `add`, it does not strip zero coefficients; see there. -/
@[simp]
def mul [CommRing R] (p q : Polynomial R n) : Polynomial R n :=
  ⟨mulTerms p.terms q.terms⟩

instance [CommRing R] : Mul (Polynomial R n) := ⟨mul⟩

def pow [CommRing R] (p : Polynomial R n) (m : Nat) : Polynomial R n := match m with
  | 0 => ⟨[.mk 1 .unit]⟩
  | .succ m' => p.mul (pow p m')

instance [CommRing R] : NatPow (Polynomial R n) := ⟨pow⟩

/-! ### Guarded multiplication

Packing exponents into one machine word is faithful only while no digit
overflows.  `mul` itself stays total -- it just adds keys -- and `mulOk` is the
kernel-checkable side condition saying that both factors are packed faithfully
and that the degrees of the product still fit in a digit.  `toPoly` consults it
and answers `none` when it fails, so soundness of the reflective checker needs
no degree hypothesis anywhere; only completeness does.
-/

/-- An upper bound for the total degree of the monomials of a term list, read
off the packed keys (`Mon.degB`) rather than the decoded exponent vectors.  It
is only ever used together with `monWFB`, where the two agree
(`Mon.degree_eq_degB`). -/
def monDegBound : List (PolyTerm R n) → Nat
  | [] => 0
  | t :: ts => max t.monomial.degB (monDegBound ts)

/-- Every monomial of the list is packed faithfully. -/
def monWFB : List (PolyTerm R n) → Bool
  | [] => true
  | t :: ts => t.monomial.wf && monWFB ts

/-- The side condition for `mul`: both factors are packed faithfully, and the
degrees of the product still fit below `Mon.base n`. -/
def mulOk (p q : Polynomial R n) : Bool :=
  monWFB p.terms && monWFB q.terms &&
    decide (monDegBound p.terms + monDegBound q.terms < Mon.base n)

/-- `mul`, refusing to answer when the packing would overflow. -/
def mulChecked [CommRing R] (p q : Polynomial R n) : Option (Polynomial R n) :=
  if mulOk p q then some (p.mul q) else none

/-- `pow`, refusing to answer when the packing would overflow. -/
def powChecked [CommRing R] (p : Polynomial R n) : Nat → Option (Polynomial R n)
  | 0 => some ⟨[⟨1, .unit⟩]⟩
  | k + 1 => (powChecked p k).bind (mulChecked p)

instance [CommRing R] : SMul R (Polynomial R n) := ⟨smul⟩

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

/--
  Sorting polynomials
-/

def grevlexTerms (p q : List (PolyTerm R n)) : Ordering :=
  match p, q with
  | [], [] => .eq
  | [], _ => .lt
  | _ , [] => .gt
  | phead::ptail, qhead::qtail =>
    match phead.monomial.grevlex qhead.monomial with
    | .eq => grevlexTerms ptail qtail
    | ord => ord

def grevlex (p q : Polynomial R n) : Ordering :=
  grevlexTerms p.terms q.terms


/--
  Comparison of polynomials using grevlex. Based on the first term where the monomial differs
  The zero polynoial is less than any other polynomial (i.e. `p.Grevlex zero`) as long as p is non-zero

  Warning: This is not trichotomous because it cannot distinguish polynomials on the same set of monomials
-/
def Grevlex (p q : Polynomial R n) : Prop := p.grevlex q = .gt


end Polynomial

end Macaulean
