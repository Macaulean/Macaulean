/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.Algebra.Defs
import Init.Grind.Ring.Field

/-!
# Standard algebra instances for `grind`

Provides the identity algebra, and the canonical Nat/Int algebra instances.
-/

namespace Lean.Grind

-- Make NatCast/IntCast from Semiring/Ring fields available as instances
attribute [local instance] Semiring.natCast Ring.intCast

namespace Field

variable {A : Type u} [Field A] [IsCharP A 0]

/-- Interpret a rational number in a characteristic-zero `grind` field. -/
def ofRat (r : Rat) : A :=
  Rat.numDenCasesOn' r fun n d _ => (n : A) / (d : A)

private theorem natCast_ne_zero (n : Nat) (hn : n ≠ 0) : (n : A) ≠ 0 := by
  intro h
  have : n = 0 := by
    simpa [Nat.mod_zero] using (IsCharP.natCast_eq_zero_iff (α := A) 0 n).mp h
  exact hn this

private theorem div_eq_of_cross
    {a b c d : A} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = c * b) :
    a / b = c / d := by
  have h' := congrArg (fun x : A => x * (b⁻¹ * d⁻¹)) h
  have hleft : a * d * (b⁻¹ * d⁻¹) = a * b⁻¹ := by
    calc
      a * d * (b⁻¹ * d⁻¹) = a * (d * (b⁻¹ * d⁻¹)) := by
          exact (Semiring.mul_assoc a d (b⁻¹ * d⁻¹))
      _ = a * (b⁻¹ * (d * d⁻¹)) := by
          rw [CommSemiring.mul_left_comm d b⁻¹ d⁻¹]
      _ = a * (b⁻¹ * 1) := by
          rw [Field.mul_inv_cancel hd]
      _ = a * b⁻¹ := by
          rw [Semiring.mul_one]
  have hright : c * b * (b⁻¹ * d⁻¹) = c * d⁻¹ := by
    calc
      c * b * (b⁻¹ * d⁻¹) = c * (b * (b⁻¹ * d⁻¹)) := by
          exact (Semiring.mul_assoc c b (b⁻¹ * d⁻¹))
      _ = c * ((b * b⁻¹) * d⁻¹) := by
          rw [Semiring.mul_assoc]
      _ = c * (1 * d⁻¹) := by
          rw [Field.mul_inv_cancel hb]
      _ = c * d⁻¹ := by
          rw [Semiring.one_mul]
  simpa [Field.div_eq_mul_inv, hleft, hright] using h'

@[simp] theorem ofRat_divInt (n : Int) {d : Nat} (hd : d ≠ 0) :
    ofRat (A := A) (Rat.divInt n (d : Int)) = (n : A) / (d : A) := by
  rw [Rat.divInt_ofNat]
  cases e : mkRat n d
  rename_i n' d' hd' red
  have emk : mkRat n d = mkRat n' d' := by
    rw [e]
    exact Rat.mk_eq_mkRat n' d' hd' red
  have hcross : n * d' = n' * d := (Rat.mkRat_eq_iff hd hd').mp emk
  have hdA : (d : A) ≠ 0 := natCast_ne_zero (A := A) d hd
  have hd'A : (d' : A) ≠ 0 := natCast_ne_zero (A := A) d' hd'
  have hcrossA : (n : A) * (d' : A) = (n' : A) * (d : A) := by
    simpa [Ring.intCast_mul, Ring.intCast_natCast, Semiring.natCast_mul] using
      congrArg (fun z : Int => (z : A)) hcross
  unfold ofRat Rat.numDenCasesOn' Rat.numDenCasesOn
  simp
  exact div_eq_of_cross (a := (n' : A)) (b := (d' : A)) (c := (n : A)) (d := (d : A))
    hd'A hdA hcrossA.symm

@[simp] theorem ofRat_intCast (n : Int) : ofRat (A := A) (n : Rat) = (n : A) := by
  have hdiv : Rat.divInt n 1 = (n : Rat) := by
    simpa using (Rat.num_divInt_den (a := (n : Rat)))
  rw [← hdiv]
  simpa [Field.div_eq_mul_inv, Field.inv_one, Semiring.natCast_one, Semiring.mul_one]
    using (ofRat_divInt (A := A) n Nat.one_ne_zero)

@[simp] theorem ofRat_natCast (n : Nat) : ofRat (A := A) (n : Rat) = (n : A) := by
  simpa [Ring.intCast_natCast] using (ofRat_intCast (A := A) (n : Int))

@[simp] theorem ofRat_zero : ofRat (A := A) (0 : Rat) = 0 := by
  simpa [Semiring.natCast_zero] using (ofRat_natCast (A := A) 0)

@[simp] theorem ofRat_one : ofRat (A := A) (1 : Rat) = 1 := by
  simpa [Semiring.natCast_one] using (ofRat_natCast (A := A) 1)

theorem ofRat_add (r s : Rat) : ofRat (A := A) (r + s) = ofRat (A := A) r + ofRat (A := A) s := by
  refine Rat.numDenCasesOn' r ?_
  intro n₁ d₁ hd₁
  refine Rat.numDenCasesOn' s ?_
  intro n₂ d₂ hd₂
  have hd₁A : (d₁ : A) ≠ 0 := natCast_ne_zero (A := A) d₁ hd₁
  have hd₂A : (d₂ : A) ≠ 0 := natCast_ne_zero (A := A) d₂ hd₂
  have hd₁I : (d₁ : Int) ≠ 0 := by simpa using hd₁
  have hd₂I : (d₂ : Int) ≠ 0 := by simpa using hd₂
  rw [Rat.divInt_add_divInt n₁ n₂ hd₁I hd₂I]
  have hmul : ((d₁ : Int) * d₂) = ((d₁ * d₂ : Nat) : Int) := by simp
  rw [hmul]
  rw [ofRat_divInt (A := A) (n₁ * d₂ + n₂ * d₁) (Nat.mul_ne_zero hd₁ hd₂)]
  rw [ofRat_divInt (A := A) n₁ hd₁, ofRat_divInt (A := A) n₂ hd₂]
  have hcancel₁ : (d₁ : A) * ((d₁ : A)⁻¹ * (d₂ : A)⁻¹) = (d₂ : A)⁻¹ := by
    rw [← Semiring.mul_assoc, Field.mul_inv_cancel hd₁A, Semiring.one_mul]
  simp [Field.div_eq_mul_inv, Field.inv_mul, Ring.intCast_add, Ring.intCast_mul,
    Ring.intCast_natCast, Semiring.natCast_mul, Semiring.left_distrib,
    Semiring.right_distrib, Semiring.mul_assoc, CommSemiring.mul_left_comm,
    Field.mul_inv_cancel hd₂A, Semiring.mul_one, hcancel₁]
  rw [CommSemiring.mul_comm ((d₁ : A)⁻¹) (n₁ : A)]

theorem ofRat_mul (r s : Rat) : ofRat (A := A) (r * s) = ofRat (A := A) r * ofRat (A := A) s := by
  refine Rat.numDenCasesOn' r ?_
  intro n₁ d₁ hd₁
  refine Rat.numDenCasesOn' s ?_
  intro n₂ d₂ hd₂
  have hd₁A : (d₁ : A) ≠ 0 := natCast_ne_zero (A := A) d₁ hd₁
  have hd₂A : (d₂ : A) ≠ 0 := natCast_ne_zero (A := A) d₂ hd₂
  rw [Rat.divInt_mul_divInt n₁ n₂]
  have hmul : ((d₁ : Int) * d₂) = ((d₁ * d₂ : Nat) : Int) := by simp
  rw [hmul]
  rw [ofRat_divInt (A := A) (n₁ * n₂) (Nat.mul_ne_zero hd₁ hd₂)]
  rw [ofRat_divInt (A := A) n₁ hd₁, ofRat_divInt (A := A) n₂ hd₂]
  simp [Field.div_eq_mul_inv, Field.inv_mul, Ring.intCast_mul, Ring.intCast_natCast,
    Semiring.natCast_mul, Semiring.mul_assoc, CommSemiring.mul_comm,
    CommSemiring.mul_left_comm, Field.mul_inv_cancel hd₁A, Field.mul_inv_cancel hd₂A]

end Field

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

/-! ### Characteristic-zero fields are Rat-algebras -/

instance (priority := 98) Field.toRatAlgebra (A : Type u) [Field A] [IsCharP A 0] :
    Algebra Rat A where
  smul := fun r a => Lean.Grind.Field.ofRat (A := A) r * a
  toFun := Lean.Grind.Field.ofRat (A := A)
  map_zero := Lean.Grind.Field.ofRat_zero (A := A)
  map_one := Lean.Grind.Field.ofRat_one (A := A)
  map_add := Lean.Grind.Field.ofRat_add (A := A)
  map_mul := Lean.Grind.Field.ofRat_mul (A := A)
  commutes := fun r x => CommSemiring.mul_comm (Lean.Grind.Field.ofRat (A := A) r) x
  smul_def := by
    intro r a
    rfl

end Lean.Grind
