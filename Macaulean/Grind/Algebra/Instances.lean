/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.Algebra.Defs

/-!
# Standard algebra instances for `grind`

Provides the identity algebra, and the canonical Nat/Int algebra instances.
-/

namespace Lean.Grind

-- Make NatCast/IntCast from Semiring/Ring fields available as instances
attribute [local instance] Semiring.natCast Ring.intCast

/-! ### Identity algebra: every commutative semiring is an algebra over itself -/

instance (priority := 1100) Algebra.selfAlgebra (R : Type u) [CommSemiring R] : Algebra R R where
  smul := (· * ·)
  toFun := _root_.id
  map_zero := by rfl
  map_one := by rfl
  map_add := by intros; rfl
  map_mul := by intros; rfl
  commutes := CommSemiring.mul_comm
  smul_def := by intros; rfl

/-! ### Every semiring is a Nat-algebra -/

instance (priority := 99) Semiring.toNatAlgebra (A : Type u) [Semiring A] : Algebra Nat A where
  smul := (· • ·)
  toFun := fun n => Nat.cast n
  map_zero := Semiring.natCast_zero
  map_one := Semiring.natCast_one
  map_add := Semiring.natCast_add
  map_mul := Semiring.natCast_mul
  commutes := Semiring.natCast_mul_comm
  smul_def := fun n a => Semiring.nsmul_eq_natCast_mul n a

/-! ### Every ring is an Int-algebra -/

instance (priority := 99) Ring.toIntAlgebra (A : Type u) [Ring A] : Algebra Int A where
  smul := (· • ·)
  toFun := fun n => Int.cast n
  map_zero := Ring.intCast_zero
  map_one := Ring.intCast_one
  map_add := Ring.intCast_add
  map_mul := Ring.intCast_mul
  commutes := Ring.intCast_mul_comm
  smul_def := fun _ _ => Ring.zsmul_eq_intCast_mul

end Lean.Grind
