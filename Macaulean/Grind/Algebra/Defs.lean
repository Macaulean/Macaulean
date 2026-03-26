/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean

/-!
# Algebra typeclass for `grind`

An `Algebra R A` structure equips a semiring `A` with a ring homomorphism from a commutative
semiring `R` into the center of `A`. This mirrors mathlib's `Algebra` but with unbundled axioms
suitable for grind's E-matching and polynomial normalization.
-/

namespace Lean.Grind

class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends SMul R A where
  toFun : R → A
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  map_add : ∀ r s : R, toFun (r + s) = toFun r + toFun s
  map_mul : ∀ r s : R, toFun (r * s) = toFun r * toFun s
  commutes : ∀ (r : R) (x : A), toFun r * x = x * toFun r
  smul_def : ∀ (r : R) (x : A), r • x = toFun r * x

attribute [instance 100] Algebra.toSMul

def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R → A :=
  Algebra.toFun

/-! ### E-matching lemmas (CommSemiring/Semiring) -/
section Semiring
variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[grind =] theorem Algebra.algebraMap_zero : algebraMap R A 0 = 0 := Algebra.map_zero
@[grind =] theorem Algebra.algebraMap_one : algebraMap R A 1 = 1 := Algebra.map_one

@[grind =] theorem Algebra.algebraMap_add (r s : R) :
    algebraMap R A (r + s) = algebraMap R A r + algebraMap R A s := Algebra.map_add r s

@[grind =] theorem Algebra.algebraMap_mul (r s : R) :
    algebraMap R A (r * s) = algebraMap R A r * algebraMap R A s := Algebra.map_mul r s

@[grind =] theorem Algebra.algebraMap_commutes (r : R) (x : A) :
    algebraMap R A r * x = x * algebraMap R A r := Algebra.commutes r x

@[grind =] theorem Algebra.algebraMap_smul_def (r : R) (x : A) :
    r • x = algebraMap R A r * x := Algebra.smul_def r x

@[grind =] theorem Algebra.algebraMap_mul_rev (r s : R) :
    algebraMap R A r * algebraMap R A s = algebraMap R A (r * s) := (Algebra.map_mul r s).symm

@[grind =] theorem Algebra.algebraMap_add_rev (r s : R) :
    algebraMap R A r + algebraMap R A s = algebraMap R A (r + s) := (Algebra.map_add r s).symm

theorem Algebra.algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) := by
  rw [Algebra.algebraMap_smul_def, Semiring.mul_one]

theorem Algebra.smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) := by
  rw [Algebra.algebraMap_smul_def, Algebra.algebraMap_smul_def, Semiring.mul_assoc]

theorem Algebra.mul_smul_comm (r : R) (x y : A) : x * r • y = r • (x * y) := by
  rw [Algebra.algebraMap_smul_def, Algebra.algebraMap_smul_def,
      ← Semiring.mul_assoc, ← algebraMap_commutes, Semiring.mul_assoc]

theorem Algebra.left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← Semiring.mul_assoc, ← algebraMap_commutes, Semiring.mul_assoc]

theorem Algebra.right_comm (x : A) (r : R) (y : A) :
    x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [Semiring.mul_assoc, algebraMap_commutes, ← Semiring.mul_assoc]

end Semiring

/-! ### Negation/subtraction lemmas (CommRing) -/
section Ring
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

theorem Algebra.algebraMap_neg (r : R) :
    algebraMap R A (-r) = -(algebraMap R A r) := by
  have h : algebraMap R A (-r) + algebraMap R A r = 0 := by
    rw [← Algebra.algebraMap_add, Ring.neg_add_cancel, Algebra.algebraMap_zero]
  calc algebraMap R A (-r)
      _ = algebraMap R A (-r) + 0 := (AddCommMonoid.add_zero _).symm
      _ = algebraMap R A (-r) + (algebraMap R A r + -(algebraMap R A r)) :=
            by rw [AddCommGroup.add_neg_cancel]
      _ = (algebraMap R A (-r) + algebraMap R A r) + -(algebraMap R A r) :=
            by rw [AddCommMonoid.add_assoc]
      _ = 0 + -(algebraMap R A r) := by rw [h]
      _ = -(algebraMap R A r) := AddCommMonoid.zero_add _

@[grind =] theorem Algebra.algebraMap_sub (r s : R) :
    algebraMap R A (r - s) = algebraMap R A r - algebraMap R A s := by
  rw [Ring.sub_eq_add_neg, Algebra.algebraMap_add, Algebra.algebraMap_neg, Ring.sub_eq_add_neg]

theorem Algebra.algebraMap_sub_rev (r s : R) :
    algebraMap R A r - algebraMap R A s = algebraMap R A (r - s) :=
  (Algebra.algebraMap_sub r s).symm

end Ring

end Lean.Grind
