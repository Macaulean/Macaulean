import Macaulean.Interpreter.KernelPolynomialWeights

/-!
# Coefficientwise polynomial and ideal semantics over commutative rings

These meanings do not identify polynomials by their values on field elements.
In particular x^p-x is a nonzero polynomial over F_p even though its evaluation
vanishes everywhere. Sparse lists are presentations; `Equivalent` forgets their
ordering, duplicate terms, and explicit zero terms.
-/
namespace Macaulean.Algebra
open Lean.Grind
open Macaulean.M2.KernelPolynomial

variable {R : Type} [CommRing R] [DecidableEq R] {n : Nat}

namespace Polynomial

def coefficient (p : Macaulean.Polynomial R n) (m : Mon n) : R :=
  weightedSum (fun k => if k = m then 1 else 0) p.terms

def Equivalent (p q : Macaulean.Polynomial R n) : Prop :=
  ∀ m, coefficient p m = coefficient q m

def zero : Macaulean.Polynomial R n := ⟨[]⟩

def productCoefficient (p q : Macaulean.Polynomial R n) (m : Mon n) : R :=
  weightedSum (fun a => weightedSum (fun b => if a.mul b = m then 1 else 0)
    q.terms) p.terms

omit [DecidableEq R] in
theorem equivalent_refl (p : Macaulean.Polynomial R n) : Equivalent p p := fun _ => rfl

omit [DecidableEq R] in
theorem equivalent_symm {p q : Macaulean.Polynomial R n} (h : Equivalent p q) :
    Equivalent q p := fun m => (h m).symm

omit [DecidableEq R] in
theorem equivalent_trans {p q t : Macaulean.Polynomial R n}
    (h : Equivalent p q) (k : Equivalent q t) : Equivalent p t :=
  fun m => (h m).trans (k m)

omit [DecidableEq R] in
theorem coefficient_zero (m : Mon n) : coefficient (zero : Macaulean.Polynomial R n) m = 0 := rfl

theorem coefficient_normalize (p : Macaulean.Polynomial R n) (m : Mon n) :
    coefficient (normalize p) m = coefficient p m := weightedSum_normalize _ _

theorem normalize_equivalent (p : Macaulean.Polynomial R n) : Equivalent (normalize p) p :=
  coefficient_normalize p

theorem equivalent_of_normalize_eq (p q : Macaulean.Polynomial R n)
    (h : normalize p = normalize q) : Equivalent p q := by
  intro m
  rw [← coefficient_normalize p m, h, coefficient_normalize]

theorem coefficient_add (p q : Macaulean.Polynomial R n) (m : Mon n) :
    coefficient (add p q) m = coefficient p m + coefficient q m := weightedSum_add _ _ _

theorem coefficient_sub (p q : Macaulean.Polynomial R n) (m : Mon n) :
    coefficient (sub p q) m = coefficient p m - coefficient q m := weightedSum_sub _ _ _

theorem coefficient_mul (p q : Macaulean.Polynomial R n) (m : Mon n) :
    coefficient (mul p q) m = productCoefficient p q m := weightedSum_mul _ _ _

end Polynomial

/-- An ideal is a coefficientwise well-defined predicate closed under zero,
addition, and multiplication by arbitrary polynomials. -/
structure Ideal (R : Type) [CommRing R] [DecidableEq R] (n : Nat) where
  contains : Macaulean.Polynomial R n → Prop
  zero_mem : contains Polynomial.zero
  add_mem : ∀ {p q}, contains p → contains q → contains (add p q)
  mul_mem : ∀ a {p}, contains p → contains (mul a p)
  equivalent_mem : ∀ {p q}, Polynomial.Equivalent p q → contains p → contains q

/-- The least ideal containing the supplied generators. -/
inductive Generated (gs : List (Macaulean.Polynomial R n)) : Macaulean.Polynomial R n → Prop
  | zero : Generated gs Polynomial.zero
  | generator {p} : p ∈ gs → Generated gs p
  | add {p q} : Generated gs p → Generated gs q → Generated gs (add p q)
  | mul (a) {p} : Generated gs p → Generated gs (mul a p)
  | equivalent {p q} : Polynomial.Equivalent p q → Generated gs p → Generated gs q

namespace Ideal

def span (gs : List (Macaulean.Polynomial R n)) : Ideal R n where
  contains := Generated gs
  zero_mem := .zero
  add_mem := .add
  mul_mem := .mul
  equivalent_mem := .equivalent

theorem span_le (gs : List (Macaulean.Polynomial R n)) (I : Ideal R n)
    (h : ∀ g ∈ gs, I.contains g) : ∀ p, (span gs).contains p → I.contains p := by
  intro p hp
  induction hp with
  | zero => exact I.zero_mem
  | generator hg => exact h _ hg
  | add _ _ ihp ihq => exact I.add_mem ihp ihq
  | mul a _ ih => exact I.mul_mem a ih
  | equivalent he _ ih => exact I.equivalent_mem he ih

/-- Equality of ideals is equality of membership, not equality of generator lists. -/
def Same (I J : Ideal R n) : Prop := ∀ p, I.contains p ↔ J.contains p

theorem span_same (gs hs : List (Macaulean.Polynomial R n))
    (forward : ∀ g ∈ gs, (span hs).contains g)
    (backward : ∀ h ∈ hs, (span gs).contains h) : Same (span gs) (span hs) :=
  fun p => ⟨span_le gs (span hs) forward p, span_le hs (span gs) backward p⟩

end Ideal
end Macaulean.Algebra
