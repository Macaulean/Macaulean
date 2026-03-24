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

The key insight is that grind's ring solver treats `HSMul R A` for general `R` as opaque.
By providing `smul_def : r • x = algebraMap r * x`, we convert scalar multiplication into
ring multiplication that the Gröbner basis can normalize.
-/

namespace Lean.Grind

/--
An associative unital `R`-algebra is a semiring `A` equipped with a ring homomorphism
`algebraMap : R → A` whose image lies in the center of `A`.

This is the grind-internal version of mathlib's `Algebra`. The ring homomorphism is unbundled:
instead of `R →+* A`, we have a plain function with explicit preservation axioms.
-/
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends SMul R A where
  /-- The algebra map from `R` to `A`. -/
  toFun : R → A
  /-- The algebra map preserves zero. -/
  map_zero : toFun 0 = 0
  /-- The algebra map preserves one. -/
  map_one : toFun 1 = 1
  /-- The algebra map preserves addition. -/
  map_add : ∀ r s : R, toFun (r + s) = toFun r + toFun s
  /-- The algebra map preserves multiplication. -/
  map_mul : ∀ r s : R, toFun (r * s) = toFun r * toFun s
  /-- The image of the algebra map commutes with all elements of `A`. -/
  commutes : ∀ (r : R) (x : A), toFun r * x = x * toFun r
  /-- Scalar multiplication is defined via the algebra map. -/
  smul_def : ∀ (r : R) (x : A), r • x = toFun r * x

attribute [instance 100] Algebra.toSMul

/-- The algebra map from `R` to `A`, extracted from the `Algebra R A` instance. -/
def algebraMap (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : R → A :=
  Algebra.toFun

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/-! ### Grind lemmas for E-matching -/

@[grind =] theorem Algebra.algebraMap_zero : algebraMap R A 0 = 0 :=
  Algebra.map_zero

@[grind =] theorem Algebra.algebraMap_one : algebraMap R A 1 = 1 :=
  Algebra.map_one

@[grind =] theorem Algebra.algebraMap_add (r s : R) :
    algebraMap R A (r + s) = algebraMap R A r + algebraMap R A s :=
  Algebra.map_add r s

@[grind =] theorem Algebra.algebraMap_mul (r s : R) :
    algebraMap R A (r * s) = algebraMap R A r * algebraMap R A s :=
  Algebra.map_mul r s

@[grind =] theorem Algebra.algebraMap_commutes (r : R) (x : A) :
    algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes r x

@[grind =] theorem Algebra.algebraMap_smul_def (r : R) (x : A) :
    r • x = algebraMap R A r * x :=
  Algebra.smul_def r x

/-! ### Derived theorems -/

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

end Lean.Grind
