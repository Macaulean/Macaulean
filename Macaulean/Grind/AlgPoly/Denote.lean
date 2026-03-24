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

/-! ### concat -/

theorem denote_concat (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.concat p₂).denote φ ctx = p₁.denote φ ctx + p₂.denote φ ctx := by
  induction p₁ with
  | coeff k =>
    show (p₂.addCoeff k).denote φ ctx = φ k + p₂.denote φ ctx
    -- addCoeff unfolds to: if k == 0 then p₂ else addCoeff.go k p₂
    -- In general, we need: addCoeff result has correct denotation
    -- This requires BEq correctness. Sorry for now.
    sorry
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
  sorry -- Induction on fuel + denote_addCoeff + denote_concat + grevlex case analysis

theorem denote_mulCoeff (hφ : IsRingHom φ) (c : C) (p : AlgPoly C) :
    (mulCoeff c p).denote φ ctx = φ c * p.denote φ ctx := by
  sorry -- Unfold mulCoeff, split on c==0/c==1, use denote_mulCoeff_go for general case

theorem denote_mulMon (hφ : IsRingHom φ) (c : C) (m : Mon) (p : AlgPoly C) :
    (mulMon c m p).denote φ ctx = φ c * m.denote ctx * p.denote φ ctx := by
  sorry -- Similar to mulCoeff: unfold, split, structural induction

theorem denote_mul (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.mul p₂).denote φ ctx = p₁.denote φ ctx * p₂.denote φ ctx := by
  sorry -- Induction on p₁ via mul.go, uses denote_combine + denote_mulCoeff + denote_mulMon

theorem denote_sub (hφ : IsRingHom φ) (p₁ p₂ : AlgPoly C) :
    (p₁.sub p₂).denote φ ctx = p₁.denote φ ctx - p₂.denote φ ctx := by
  show (p₁.combine p₂.neg).denote φ ctx = _
  rw [denote_combine _ _ hφ, denote_neg _ _ hφ, Ring.sub_eq_add_neg]

theorem denote_pow (hφ : IsRingHom φ) (p : AlgPoly C) (k : Nat) :
    (p.pow k).denote φ ctx = p.denote φ ctx ^ k := by
  sorry -- Induction on k, uses denote_mul + Semiring.pow_succ

end Macaulean.AlgPoly
