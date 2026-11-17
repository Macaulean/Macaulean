import Lean
import Init.GrindInstances.Ring.Fin
import Init.Grind.Ring.Field

/-!
# Checked prime coefficient fields

Elements are residues `Fin (n+2)`, with the standard modular commutative-ring
operations. A characteristic is accepted only with a kernel-checkable proof that
the executable inverse is an inverse of every nonzero residue. This directly
establishes the field laws; a composite modulus cannot be accepted as a field.
The exhaustive check is intended for small characteristics in this first bridge.
-/
namespace Macaulean.Algebra.PrimeField
open Lean.Grind

abbrev Element (n : Nat) := Fin (n + 2)

def inverse (a : Element n) : Element n :=
  if a = 0 then 0 else a ^ n

/-- The inverse law is checked over all residues, not assumed from a field tag. -/
def Valid (n : Nat) : Prop := ∀ a : Element n, a ≠ 0 → a * inverse a = 1

instance (n : Nat) : Decidable (Valid n) := inferInstanceAs
  (Decidable (∀ a : Fin (n+2), a ≠ 0 → a * inverse a = 1))

@[simp] theorem inverse_zero : inverse (0 : Element n) = 0 := by simp [inverse]

theorem zero_ne_one : (0 : Element n) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem inverse_unique (h : Valid n) (a b : Element n) (hab : a*b = 1) :
    b = inverse a := by
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp [Semiring.zero_mul] at hab
  have hi := h a ha
  calc
    b = b * (a * inverse a) := by rw [hi, Semiring.mul_one]
    _ = (a*b) * inverse a := by grind
    _ = inverse a := by rw [hab, Semiring.one_mul]

theorem inverse_inverse (h : Valid n) (a : Element n) : inverse (inverse a) = a := by
  by_cases ha : a = 0
  · subst a; simp
  · symm
    apply inverse_unique h
    rw [CommSemiring.mul_comm]
    exact h a ha

theorem inverse_one (h : Valid n) : inverse (1 : Element n) = 1 := by
  symm
  exact inverse_unique h 1 1 (Semiring.one_mul 1)

def integerPower (a : Element n) : Int → Element n
  | .ofNat k => a ^ k
  | .negSucc k => inverse (a ^ (k+1))

/-- A standard Lean field instance, constructed from the checked inverse law. -/
@[implicit_reducible]
def field (h : Valid n) : Field (Element n) where
  toCommRing := inferInstance
  inv := inverse
  div a b := a * inverse b
  zpow := ⟨integerPower⟩
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := zero_ne_one
  inv_zero := inverse_zero
  mul_inv_cancel := h _
  zpow_zero _ := rfl
  zpow_succ _ _ := rfl
  zpow_neg a k := by
    cases k with
    | ofNat k =>
      cases k with
      | zero => exact (inverse_one h).symm
      | succ k => rfl
    | negSucc k => exact (inverse_inverse h (a ^ (k+1))).symm

/-- The package carries the field proof with its characteristic. -/
structure Checked where
  offset : Nat
  valid : Valid offset

def Checked.characteristic (F : Checked) : Nat := F.offset + 2
abbrev Checked.Carrier (F : Checked) := Element F.offset
instance (F : Checked) : Field F.Carrier := field F.valid

/-- Failure publishes no field. Characteristics zero and one are rejected before
checking the finite inverse table. -/
def check : Nat → Except String Checked
  | 0 | 1 => .error "a prime field characteristic must be at least two"
  | n+2 => if h : Valid n then .ok ⟨n,h⟩
      else .error "the characteristic does not define a prime field"

end Macaulean.Algebra.PrimeField
