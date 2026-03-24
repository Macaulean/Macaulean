/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Basic

/-!
# Denotation correctness theorems for AlgPoly

These theorems prove that AlgPoly operations preserve semantics under denotation.
They are the proof certificates for proof-by-reflection: if two AlgPoly values
are structurally equal after normalization, their denotations are equal.

## Key theorems

- `denote_combine`: `(p₁.combine p₂).denote φ ctx = p₁.denote φ ctx + p₂.denote φ ctx`
- `denote_mul`: `(p₁.mul p₂).denote φ ctx = p₁.denote φ ctx * p₂.denote φ ctx`
- `denote_neg`: `p.neg.denote φ ctx = -(p.denote φ ctx)`

## Morphism requirements

The morphism `φ : C → A` must be a ring homomorphism:
- `φ 0 = 0`, `φ 1 = 1`
- `φ (a + b) = φ a + φ b`
- `φ (a * b) = φ a * φ b`
- `φ (-a) = -(φ a)`

This is exactly what `Algebra.algebraMap` provides.
-/

open Lean.Grind
open Lean.Grind.CommRing (Var Power Mon)

namespace Macaulean.AlgPoly

variable {C : Type u} {A : Type v} [CoeffRing C] [CommRing A]
variable (φ : C → A) (ctx : CommRing.Context A)

variable (hφ : IsRingHom φ)

/-! ### Additive operation correctness -/

theorem denote_addCoeff (p : AlgPoly C) (c : C) :
    (p.addCoeff c).denote φ ctx = p.denote φ ctx + φ c := by
  sorry

theorem denote_concat (p₁ p₂ : AlgPoly C) :
    (p₁.concat p₂).denote φ ctx = p₁.denote φ ctx + p₂.denote φ ctx := by
  sorry

theorem denote_combine (p₁ p₂ : AlgPoly C) :
    (p₁.combine p₂).denote φ ctx = p₁.denote φ ctx + p₂.denote φ ctx := by
  sorry

/-! ### Multiplicative operation correctness -/

theorem denote_mulCoeff (c : C) (p : AlgPoly C) :
    (mulCoeff c p).denote φ ctx = φ c * p.denote φ ctx := by
  sorry

theorem denote_mulMon (c : C) (m : Mon) (p : AlgPoly C) :
    (mulMon c m p).denote φ ctx = φ c * m.denote ctx * p.denote φ ctx := by
  sorry

theorem denote_mul (p₁ p₂ : AlgPoly C) :
    (p₁.mul p₂).denote φ ctx = p₁.denote φ ctx * p₂.denote φ ctx := by
  sorry

/-! ### Negation/subtraction correctness -/

theorem denote_neg (p : AlgPoly C) :
    p.neg.denote φ ctx = -(p.denote φ ctx) := by
  sorry

theorem denote_sub (p₁ p₂ : AlgPoly C) :
    (p₁.sub p₂).denote φ ctx = p₁.denote φ ctx - p₂.denote φ ctx := by
  sorry

/-! ### Power correctness -/

theorem denote_pow (p : AlgPoly C) (k : Nat) :
    (p.pow k).denote φ ctx = p.denote φ ctx ^ k := by
  sorry

end Macaulean.AlgPoly
