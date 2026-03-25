/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Basic

/-!
# Denotation correctness theorems for AlgPoly
-/

open Lean.Grind
open Lean.Grind.CommRing (Var Power Mon)

namespace Macaulean.AlgPoly

variable {C : Type u} {A : Type v} [CoeffRing C] [CommRing A]
variable (φ : C → A) (ctx : CommRing.Context A)

/-! ### Negation -/

theorem denote_neg (hφ : IsRingHom φ) (p : AlgPoly C) :
    p.neg.denote φ ctx = -(p.denote φ ctx) := by
  induction p with
  | coeff k =>
    exact IsRingHom.map_neg hφ k
  | add k m p ih =>
    show φ (-k) * m.denote ctx + p.neg.denote φ ctx =
         -(φ k * m.denote ctx + p.denote φ ctx)
    rw [IsRingHom.map_neg hφ, ih, Ring.neg_mul, AddCommGroup.neg_add]

/-! ### addCoeff.go -/

private theorem denote_addCoeff_go (hφ : IsRingHom φ) (p : AlgPoly C) (c : C) :
    (addCoeff.go c p).denote φ ctx = p.denote φ ctx + φ c := by
  induction p with
  | coeff k =>
    exact IsRingHom.map_add hφ k c
  | add k m p ih =>
    show φ k * m.denote ctx + (addCoeff.go c p).denote φ ctx =
         φ k * m.denote ctx + p.denote φ ctx + φ c
    rw [ih, Semiring.add_assoc]

theorem denote_addCoeff (hφ : IsRingHom φ) (p : AlgPoly C) (c : C) :
    (p.addCoeff c).denote φ ctx = p.denote φ ctx + φ c := by
  unfold addCoeff
  split
  · rename_i h; have := Macaulean.CoeffRing.beq_sound _ _ h; subst this
    rw [IsRingHom.map_zero hφ, Semiring.add_zero]
  · exact denote_addCoeff_go φ ctx hφ p c

/-! ### concat -/

theorem denote_concat (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.concat p₂).denote φ ctx = p₁.denote φ ctx + p₂.denote φ ctx := by
  induction p₁ with
  | coeff k =>
    show (p₂.addCoeff k).denote φ ctx = φ k + p₂.denote φ ctx
    rw [denote_addCoeff _ _ hφ, Semiring.add_comm]
  | add k m p₁ ih =>
    show φ k * m.denote ctx + (p₁.concat p₂).denote φ ctx =
         φ k * m.denote ctx + p₁.denote φ ctx + p₂.denote φ ctx
    rw [ih, Semiring.add_assoc]

/-! ### mulCoeff.go -/

private theorem denote_mulCoeff_go (hφ : IsRingHom φ) (c : C) (p : AlgPoly C) :
    (mulCoeff.go c p).denote φ ctx = φ c * p.denote φ ctx := by
  induction p with
  | coeff k =>
    exact IsRingHom.map_mul hφ c k
  | add k m p ih =>
    show φ (c * k) * m.denote ctx + (mulCoeff.go c p).denote φ ctx =
         φ c * (φ k * m.denote ctx + p.denote φ ctx)
    rw [IsRingHom.map_mul hφ, ih, Semiring.left_distrib, Semiring.mul_assoc]

/-! ### Remaining theorems (sorry'd — clear dependency structure) -/

theorem denote_combine (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.combine p₂).denote φ ctx = p₁.denote φ ctx + p₂.denote φ ctx := by
  sorry -- Fuel-based induction on combine.go with grevlex case analysis.
        -- Structure proven: base cases (concat, addCoeff) are correct.
        -- Remaining: ring rearrangement in the grevlex eq/gt/lt cases.

theorem denote_mulCoeff (hφ : IsRingHom φ) (c : C) (p : AlgPoly C) :
    (mulCoeff c p).denote φ ctx = φ c * p.denote φ ctx := by
  unfold mulCoeff
  split
  · -- c == 0
    rename_i h
    have hc := Macaulean.CoeffRing.beq_sound _ _ h
    subst hc
    simp [denote, IsRingHom.map_zero hφ, Semiring.zero_mul]
  · split
    · -- c == 1
      rename_i _ h
      have hc := Macaulean.CoeffRing.beq_sound _ _ h
      subst hc
      simp [IsRingHom.map_one hφ, Semiring.one_mul]
    · -- general
      exact denote_mulCoeff_go φ ctx hφ c p

private theorem denote_mulMon_go (hφ : IsRingHom φ) (c : C) (m : Mon) (p : AlgPoly C) :
    (mulMon.go c m p).denote φ ctx = φ c * m.denote ctx * p.denote φ ctx := by
  induction p with
  | coeff k =>
    unfold mulMon.go
    split
    · -- k == 0
      rename_i h; have hk := Macaulean.CoeffRing.beq_sound _ _ h; subst hk
      simp [denote, IsRingHom.map_zero hφ, Semiring.mul_zero, IsRingHom.map_mul hφ]
    · -- k ≠ 0
      simp only [denote, IsRingHom.map_mul hφ, IsRingHom.map_zero hφ, Semiring.add_zero]
      rw [Semiring.mul_assoc, CommSemiring.mul_comm (φ k) (m.denote ctx), ← Semiring.mul_assoc]
  | add k m' p ih =>
    simp only [mulMon.go, denote]
    rw [IsRingHom.map_mul hφ]
    rw [CommRing.Mon.denote_mul, ih]
    rw [Semiring.left_distrib, Semiring.mul_assoc, Semiring.mul_assoc, Semiring.mul_assoc]
    congr 1
    rw [← Semiring.mul_assoc (φ k), CommSemiring.mul_comm (φ k) (Mon.denote ctx m),
        Semiring.mul_assoc]

theorem denote_mulMon (hφ : IsRingHom φ) (c : C) (m : Mon) (p : AlgPoly C) :
    (mulMon c m p).denote φ ctx = φ c * m.denote ctx * p.denote φ ctx := by
  unfold mulMon
  split
  · -- c == 0
    rename_i h; have hc := Macaulean.CoeffRing.beq_sound _ _ h; subst hc
    simp [denote, IsRingHom.map_zero hφ, Semiring.zero_mul]
  · split
    · -- m == unit
      rename_i _ h
      rename_i _ h
      have hm : m = Mon.unit := eq_of_beq h
      subst hm
      simp [Mon.denote, Semiring.mul_one, denote_mulCoeff _ _ hφ]
    · exact denote_mulMon_go φ ctx hφ c m p

private theorem denote_mul_go (hφ : IsRingHom φ) (p₂ : AlgPoly C)
    (p₁ acc : AlgPoly C) :
    (mul.go p₂ p₁ acc).denote φ ctx =
    acc.denote φ ctx + p₁.denote φ ctx * p₂.denote φ ctx := by
  induction p₁ generalizing acc with
  | coeff k =>
    show (acc.combine (p₂.mulCoeff k)).denote φ ctx = _
    simp only [denote]
    rw [denote_combine _ _ hφ, denote_mulCoeff _ _ hφ]
  | add k m p₁ ih =>
    simp only [mul.go]
    rw [ih]
    rw [denote_combine _ _ hφ, denote_mulMon _ _ hφ]
    simp only [denote]
    rw [Semiring.right_distrib, Semiring.add_assoc]

theorem denote_mul (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.mul p₂).denote φ ctx = p₁.denote φ ctx * p₂.denote φ ctx := by
  simp only [mul]
  rw [denote_mul_go _ _ hφ]
  simp [denote, IsRingHom.map_zero hφ, AddCommMonoid.zero_add]

theorem denote_sub (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.sub p₂).denote φ ctx = p₁.denote φ ctx - p₂.denote φ ctx := by
  show (p₁.combine p₂.neg).denote φ ctx = _
  rw [denote_combine _ _ hφ, denote_neg _ _ hφ, Ring.sub_eq_add_neg]

theorem denote_pow (hφ : IsRingHom φ) (p : AlgPoly C) : (k : Nat) →
    (p.pow k).denote φ ctx = p.denote φ ctx ^ k
  | 0 => by
    -- pow 0 = one = .add 1 .unit (.coeff 0)
    simp [pow, one, denote, IsRingHom.map_one hφ, IsRingHom.map_zero hφ,
          CommRing.Mon.denote, Semiring.mul_one, Semiring.add_zero, Semiring.pow_zero]
  | 1 => by simp [pow, Semiring.pow_succ, Semiring.pow_zero, Semiring.one_mul]
  | k + 2 => by
    show (p.mul (p.pow (k + 1))).denote φ ctx = _
    rw [denote_mul _ _ hφ, denote_pow hφ p (k + 1), Semiring.pow_succ (n := k)]
    -- a * (a^k * a) = a^(k+2)
    grind

end Macaulean.AlgPoly
