/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Denote

/-!
# AlgExpr: Unsimplified algebraic expressions

`AlgExpr C` represents algebraic expressions before normalization.
Analogous to `Lean.Grind.CommRing.Expr` but with parameterized coefficients.

The key function is `toAlgPoly : AlgExpr C → AlgPoly C` which normalizes
an expression into canonical polynomial form.

The reflection theorem `denote_toAlgPoly` proves normalization preserves semantics:
  `(e.toAlgPoly).denote φ ctx = e.denote φ ctx`

This is the certificate that powers the verification tactic.
-/

open Lean.Grind.CommRing (Var Power Mon)

namespace Macaulean

/--
Algebraic expression with coefficients in `C`.
This is the "reified" form of a Lean expression, before normalization.
-/
inductive AlgExpr (C : Type u) where
  | coeff (k : C)          -- a coefficient from C (maps via φ)
  | var (i : Var)           -- a variable in A
  | add (a b : AlgExpr C)  -- a + b
  | mul (a b : AlgExpr C)  -- a * b
  | neg (a : AlgExpr C)    -- -a
  | sub (a b : AlgExpr C)  -- a - b
  | pow (a : AlgExpr C) (k : Nat) -- a ^ k
  deriving Inhabited, Repr

namespace AlgExpr

variable {C : Type u} [CoeffRing C]

/-! ### Denotation -/

/-- Denote an expression into ring A via morphism φ and variable context. -/
noncomputable def denote {A : Type v} [Lean.Grind.CommRing A]
    (φ : C → A) (ctx : Lean.Grind.CommRing.Context A) : AlgExpr C → A
  | .coeff k => φ k
  | .var i => i.denote ctx
  | .add a b => a.denote φ ctx + b.denote φ ctx
  | .mul a b => a.denote φ ctx * b.denote φ ctx
  | .neg a => -(a.denote φ ctx)
  | .sub a b => a.denote φ ctx - b.denote φ ctx
  | .pow a k => a.denote φ ctx ^ k

/-! ### Normalization to AlgPoly -/

/-- Normalize an expression to canonical polynomial form. -/
def toAlgPoly : AlgExpr C → AlgPoly C
  | .coeff k => .coeff k
  | .var x => AlgPoly.ofVar x
  | .add a b => (a.toAlgPoly).combine (b.toAlgPoly)
  | .mul a b => (a.toAlgPoly).mul (b.toAlgPoly)
  | .neg a => (a.toAlgPoly).neg
  | .sub a b => (a.toAlgPoly).sub (b.toAlgPoly)
  | .pow a k => (a.toAlgPoly).pow k

/-! ### The reflection theorem -/

/-- Normalization preserves semantics. This is the proof certificate. -/
theorem denote_toAlgPoly {A : Type v} [Lean.Grind.CommRing A]
    (φ : C → A) (ctx : Lean.Grind.CommRing.Context A) (hφ : AlgPoly.IsRingHom φ)
    (e : AlgExpr C) :
    (e.toAlgPoly).denote φ ctx = e.denote φ ctx := by
  induction e with
  | coeff k => rfl
  | var i =>
    show AlgPoly.denote φ ctx (AlgPoly.ofVar i) = _
    simp [AlgPoly.ofVar, AlgPoly.denote, AlgPoly.IsRingHom.map_one hφ,
          Lean.Grind.Semiring.one_mul, AlgPoly.IsRingHom.map_zero hφ,
          Lean.Grind.Semiring.add_zero, Lean.Grind.CommRing.Mon.denote]
    simp [Lean.Grind.CommRing.Mon.ofVar, Lean.Grind.CommRing.Mon.denote,
          Lean.Grind.CommRing.Power.denote, Lean.Grind.Semiring.mul_one, denote]
  | add a b iha ihb =>
    simp only [toAlgPoly, denote]
    rw [AlgPoly.denote_combine φ ctx hφ, iha, ihb]
  | mul a b iha ihb =>
    simp only [toAlgPoly, denote]
    rw [AlgPoly.denote_mul φ ctx hφ, iha, ihb]
  | neg a ih =>
    simp only [toAlgPoly, denote]
    rw [AlgPoly.denote_neg φ ctx hφ, ih]
  | sub a b iha ihb =>
    simp only [toAlgPoly, denote]
    rw [AlgPoly.denote_sub φ ctx hφ, iha, ihb]
  | pow a k ih =>
    simp only [toAlgPoly, denote]
    rw [AlgPoly.denote_pow φ ctx hφ, ih]

end AlgExpr

/-! ### The main verification theorem -/

/--
If two expressions normalize to the same AlgPoly, they denote the same value.
This is the top-level theorem the verification tactic uses.
-/
theorem AlgExpr.eq_of_toAlgPoly_eq {C : Type u} {A : Type v}
    [CoeffRing C] [Lean.Grind.CommRing A]
    (φ : C → A) (ctx : Lean.Grind.CommRing.Context A) (hφ : AlgPoly.IsRingHom φ)
    (e₁ e₂ : AlgExpr C)
    (h : e₁.toAlgPoly.beq e₂.toAlgPoly = true) :
    e₁.denote φ ctx = e₂.denote φ ctx := by
  rw [← denote_toAlgPoly φ ctx hφ e₁, ← denote_toAlgPoly φ ctx hφ e₂]
  sorry -- needs: beq = true → equal → denotes equal (AlgPoly.beq_sound)

end Macaulean
