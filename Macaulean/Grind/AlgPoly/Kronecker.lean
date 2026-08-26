/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Macaulean.Grind.AlgPoly.Expr

@[expose] public section

/-!
# Kronecker-packed normal form for `AlgExpr`

`AlgExpr.toAlgPoly` normalizes into `AlgPoly`, whose monomials are grind's
cons-list `Mon`, so every comparison and multiplication during
normalization is a structural list traversal.  Measured on certificate
identities (`MacauleanTest/AlgebraNormPerf.lean`, tactic time only, goals
pre-built as `Expr`s), the cons-list route costs 0.5 s / 9.6 s / 64 s /
252 s at 41 / 296 / 755 / 1350 monomials of expanded product.

This module provides a second normal form for the same `AlgExpr` syntax
that replaces those traversals with single GMP operations; on the same
benchmarks the pipeline drops to 0.25 s / 2.7 s / 15 s / 37 s — a 2–7×
speedup that grows with size.
Monomials are packed into a single `Nat` key by Kronecker substitution

    x₀^e₀ * x₁^e₁ * ⋯ * xₙ^eₙ  ↦  e₀ + e₁·D + e₂·D² + ⋯ + eₙ·Dⁿ

for a base `D` larger than any exponent that can occur.  Key comparison and
monomial multiplication (`k₁ + k₂`) are then single GMP operations in the
kernel, which is what makes kernel-side normalization feasible at the
1000-monomial scale.

Two parameters are chosen by the caller (in practice: the tactic):

* `D` — the digit base; must exceed every per-variable exponent arising
  during normalization;
* `nv` — the number of digits (= number of ambient variables) interpreted by
  the denotation.

Neither choice is trusted.  Every monomial product is guarded digit-by-digit
(`mulKeyOk`), variables are range-checked against `nv`, `D > 1` is checked up
front, and the whole evaluation is `Option`-valued.  A bad choice of `D` or
`nv` can therefore only make `checkKEq` return `false` (and the tactic fail
over to another strategy) — it can never produce an unsound result, and the
soundness theorem `AlgExpr.eq_of_toKPoly_eq` has no degree side conditions.

All recursion is structural (with fuel where two arguments shrink), so the
kernel can evaluate `checkKEq` via `decide` — no `native_decide`.
-/

open Lean.Grind.CommRing (Var Power Mon Context)

set_option linter.unusedSectionVars false

namespace Macaulean

/--
Sparse polynomial in Kronecker-packed form: a `(key, coefficient)` list.
The operations below keep it sorted by ascending key with no duplicate keys,
but soundness never relies on that invariant — only completeness does.
-/
abbrev KPoly (C : Type u) := List (Nat × C)

namespace KPoly

variable {C : Type u} [CoeffRing C]

/-! ### Kernel-side operations -/

/-- Merge fuel.  Fuel only bounds the recursion depth actually taken, so a
huge literal costs nothing; the fuel-0 fallback (`++`) is denotation-correct,
merely unsorted, so running out of fuel could only cost completeness, never
soundness.  (This deliberately avoids the silent 10000-term cliff of
`AlgPoly.combine`.) -/
def mergeFuel : Nat := 1000000000

/-- Merge two key-sorted lists, adding coefficients on equal keys.
Zero coefficients are kept (`canon` strips them at the end). -/
def mergeF : Nat → KPoly C → KPoly C → KPoly C
  | 0, l₁, l₂ => l₁ ++ l₂
  | _+1, [], l₂ => l₂
  | _+1, t :: l₁, [] => t :: l₁
  | fuel+1, t₁ :: l₁, t₂ :: l₂ =>
    bif t₁.1.blt t₂.1 then t₁ :: mergeF fuel l₁ (t₂ :: l₂)
    else bif t₂.1.blt t₁.1 then t₂ :: mergeF fuel (t₁ :: l₁) l₂
    else (t₁.1, t₁.2 + t₂.2) :: mergeF fuel l₁ l₂

/-- Addition of packed polynomials. -/
def addK (l₁ l₂ : KPoly C) : KPoly C := mergeF mergeFuel l₁ l₂

/-- Digit-by-digit overflow guard for multiplying monomial keys: the first
`fuel` digit pairs must sum below the base.  Digits beyond `fuel` are not
interpreted by `monDenote` at matching fuel, so `true` at fuel 0 is sound. -/
def mulKeyOk (D : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel+1, k₁, k₂ =>
    (k₁ % D + k₂ % D).blt D && mulKeyOk D fuel (k₁ / D) (k₂ / D)

/-- Multiply every term of `l` by the single term `t`, guarding key addition.
Key translation is order-preserving, so sortedness is maintained. -/
def scaleK? (D nv : Nat) (t : Nat × C) : KPoly C → Option (KPoly C)
  | [] => some []
  | t' :: l =>
    bif mulKeyOk D nv t.1 t'.1 then
      match scaleK? D nv t l with
      | some r => some ((t.1 + t'.1, t.2 * t'.2) :: r)
      | none => none
    else none

/-- Product core: distribute the first factor over the second. -/
def mulCore? (D nv : Nat) : KPoly C → KPoly C → Option (KPoly C)
  | [], _ => some []
  | t :: l₁, l₂ =>
    match scaleK? D nv t l₂, mulCore? D nv l₁ l₂ with
    | some s, some r => some (addK s r)
    | _, _ => none

/-- Product; the shorter factor is distributed over the longer one, which
minimizes the number of merge passes. -/
def mulK? (D nv : Nat) (l₁ l₂ : KPoly C) : Option (KPoly C) :=
  bif l₁.length.ble l₂.length then mulCore? D nv l₁ l₂ else mulCore? D nv l₂ l₁

/-- Power by iterated multiplication. -/
def powK? (D nv : Nat) (l : KPoly C) : Nat → Option (KPoly C)
  | 0 => some [(0, 1)]
  | k+1 =>
    match powK? D nv l k with
    | some r => mulK? D nv l r
    | none => none

/-- Negate all coefficients (keys unchanged, so no guard is needed). -/
def negK (l : KPoly C) : KPoly C :=
  l.map fun t => (t.1, -t.2)

/-- Strip zero coefficients (cancellation leaves them behind). -/
def canon : KPoly C → KPoly C
  | [] => []
  | t :: l => bif t.2 == 0 then canon l else t :: canon l

/-- Structural equality; keys compare with GMP-backed `Nat.beq`. -/
def beqK : KPoly C → KPoly C → Bool
  | [], [] => true
  | t₁ :: l₁, t₂ :: l₂ => t₁.1.beq t₂.1 && t₁.2 == t₂.2 && beqK l₁ l₂
  | _, _ => false

/-! ### Denotation -/

variable {A : Type v} [Lean.Grind.CommRing A]

open Lean.Grind

/-- Denote a packed monomial key: digit `i` (base `D`) is the exponent of
variable `idx + i`; only the first `fuel` digits are interpreted. -/
noncomputable def monDenote (D : Nat) (ctx : Context A) : Nat → Nat → Nat → A
  | 0, _, _ => 1
  | fuel+1, idx, key =>
    Var.denote ctx idx ^ (key % D) * monDenote D ctx fuel (idx + 1) (key / D)

/-- Denote a packed polynomial via the coefficient morphism `φ`. -/
noncomputable def denote (φ : C → A) (ctx : Context A) (D nv : Nat) : KPoly C → A
  | [] => 0
  | t :: l => φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l

/-! ### Arithmetic helper lemmas -/

/-- Base-`D` digits add without carries when each digit pair sums below `D`. -/
theorem mod_div_add_carryfree {D k₁ k₂ : Nat} (hD : 0 < D)
    (h : k₁ % D + k₂ % D < D) :
    (k₁ + k₂) % D = k₁ % D + k₂ % D ∧ (k₁ + k₂) / D = k₁ / D + k₂ / D := by
  have hsum : k₁ + k₂ = (k₁ % D + k₂ % D) + (k₁ / D + k₂ / D) * D := by
    have h₁ := Nat.div_add_mod k₁ D
    have h₂ := Nat.div_add_mod k₂ D
    have hd : (k₁ / D + k₂ / D) * D = D * (k₁ / D) + D * (k₂ / D) := by
      rw [Nat.add_mul, Nat.mul_comm (k₁ / D) D, Nat.mul_comm (k₂ / D) D]
    omega
  refine ⟨?_, ?_⟩
  · rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
  · rw [hsum, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt h, Nat.zero_add]

/-! ### Denotation lemmas for monomial keys -/

theorem monDenote_zero (D : Nat) (ctx : Context A) (fuel idx : Nat) :
    monDenote D ctx fuel idx 0 = 1 := by
  induction fuel generalizing idx with
  | zero => rfl
  | succ fuel ih =>
    show Var.denote ctx idx ^ (0 % D) * monDenote D ctx fuel (idx + 1) (0 / D) = 1
    rw [Nat.zero_mod, Nat.zero_div, ih, Semiring.pow_zero, Semiring.one_mul]

theorem monDenote_mul {D : Nat} (hD : 0 < D) (ctx : Context A)
    {fuel k₁ k₂ : Nat} (h : mulKeyOk D fuel k₁ k₂ = true) (idx : Nat) :
    monDenote D ctx fuel idx (k₁ + k₂) =
      monDenote D ctx fuel idx k₁ * monDenote D ctx fuel idx k₂ := by
  induction fuel generalizing k₁ k₂ idx with
  | zero => show (1 : A) = 1 * 1; rw [Semiring.one_mul]
  | succ fuel ih =>
    simp only [mulKeyOk, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hdig, hrest⟩ := h
    obtain ⟨hmod, hdiv⟩ := mod_div_add_carryfree hD hdig
    show Var.denote ctx idx ^ ((k₁ + k₂) % D) *
        monDenote D ctx fuel (idx + 1) ((k₁ + k₂) / D) =
      Var.denote ctx idx ^ (k₁ % D) * monDenote D ctx fuel (idx + 1) (k₁ / D) *
        (Var.denote ctx idx ^ (k₂ % D) * monDenote D ctx fuel (idx + 1) (k₂ / D))
    rw [hmod, hdiv, ih hrest, Semiring.pow_add]
    grind

theorem monDenote_var {D : Nat} (hD : 1 < D) (ctx : Context A)
    {fuel i : Nat} (hi : i < fuel) (idx : Nat) :
    monDenote D ctx fuel idx (D ^ i) = Var.denote ctx (idx + i) := by
  have hD0 : 0 < D := Nat.lt_trans Nat.zero_lt_one hD
  induction fuel generalizing i idx with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ fuel ih =>
    match i with
    | 0 =>
      show Var.denote ctx idx ^ (D ^ 0 % D) *
          monDenote D ctx fuel (idx + 1) (D ^ 0 / D) = _
      rw [Nat.pow_zero, Nat.mod_eq_of_lt hD, Nat.div_eq_of_lt hD, monDenote_zero,
        Semiring.pow_one, Semiring.mul_one, Nat.add_zero]
    | i + 1 =>
      show Var.denote ctx idx ^ (D ^ (i + 1) % D) *
          monDenote D ctx fuel (idx + 1) (D ^ (i + 1) / D) = _
      rw [Nat.pow_succ, Nat.mul_mod_left, Nat.mul_div_cancel _ hD0,
        Semiring.pow_zero, Semiring.one_mul, ih (Nat.lt_of_succ_lt_succ hi)]
      rw [Nat.add_assoc, Nat.add_comm 1 i]

/-! ### Denotation lemmas for the list operations -/

variable (φ : C → A) (ctx : Context A)

theorem denote_append (D nv : Nat) (l₁ l₂ : KPoly C) :
    denote φ ctx D nv (l₁ ++ l₂) = denote φ ctx D nv l₁ + denote φ ctx D nv l₂ := by
  induction l₁ with
  | nil =>
    show denote φ ctx D nv l₂ = 0 + denote φ ctx D nv l₂
    grind
  | cons t l₁ ih =>
    show φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv (l₁ ++ l₂) =
      φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l₁ + denote φ ctx D nv l₂
    rw [ih]
    grind

theorem denote_mergeF (hφ : AlgPoly.IsRingHom φ) (D nv : Nat)
    (fuel : Nat) (l₁ l₂ : KPoly C) :
    denote φ ctx D nv (mergeF fuel l₁ l₂) =
      denote φ ctx D nv l₁ + denote φ ctx D nv l₂ := by
  induction fuel generalizing l₁ l₂ with
  | zero => exact denote_append φ ctx D nv l₁ l₂
  | succ fuel ih =>
    match l₁, l₂ with
    | [], l₂ =>
      show denote φ ctx D nv l₂ = 0 + denote φ ctx D nv l₂
      grind
    | t :: l₁, [] =>
      show denote φ ctx D nv (t :: l₁) = denote φ ctx D nv (t :: l₁) + 0
      grind
    | t₁ :: l₁, t₂ :: l₂ =>
      simp only [mergeF]
      cases hb₁ : t₁.1.blt t₂.1 with
      | true =>
        simp only [cond_true]
        show φ t₁.2 * monDenote D ctx nv 0 t₁.1 +
            denote φ ctx D nv (mergeF fuel l₁ (t₂ :: l₂)) =
          φ t₁.2 * monDenote D ctx nv 0 t₁.1 + denote φ ctx D nv l₁ +
            denote φ ctx D nv (t₂ :: l₂)
        rw [ih]
        grind
      | false =>
        simp only [cond_false]
        cases hb₂ : t₂.1.blt t₁.1 with
        | true =>
          simp only [cond_true]
          show φ t₂.2 * monDenote D ctx nv 0 t₂.1 +
              denote φ ctx D nv (mergeF fuel (t₁ :: l₁) l₂) =
            denote φ ctx D nv (t₁ :: l₁) +
              (φ t₂.2 * monDenote D ctx nv 0 t₂.1 + denote φ ctx D nv l₂)
          rw [ih]
          grind
        | false =>
          simp only [cond_false]
          have hk : t₁.1 = t₂.1 := by
            have h₁ : ¬ t₁.1 < t₂.1 := fun hlt =>
              Bool.noConfusion ((Nat.blt_eq.mpr hlt).symm.trans hb₁)
            have h₂ : ¬ t₂.1 < t₁.1 := fun hlt =>
              Bool.noConfusion ((Nat.blt_eq.mpr hlt).symm.trans hb₂)
            omega
          show φ (t₁.2 + t₂.2) * monDenote D ctx nv 0 t₁.1 +
              denote φ ctx D nv (mergeF fuel l₁ l₂) =
            φ t₁.2 * monDenote D ctx nv 0 t₁.1 + denote φ ctx D nv l₁ +
              (φ t₂.2 * monDenote D ctx nv 0 t₂.1 + denote φ ctx D nv l₂)
          rw [ih, hφ.map_add, ← hk]
          grind

theorem denote_addK (hφ : AlgPoly.IsRingHom φ) {D nv : Nat} (l₁ l₂ : KPoly C) :
    denote φ ctx D nv (addK l₁ l₂) = denote φ ctx D nv l₁ + denote φ ctx D nv l₂ :=
  denote_mergeF φ ctx hφ D nv mergeFuel l₁ l₂

theorem denote_scaleK? {D : Nat} (hD : 0 < D) (hφ : AlgPoly.IsRingHom φ)
    (nv : Nat) (t : Nat × C) (l : KPoly C) :
    ∀ r : KPoly C, scaleK? D nv t l = some r →
      denote φ ctx D nv r = φ t.2 * monDenote D ctx nv 0 t.1 * denote φ ctx D nv l := by
  induction l with
  | nil =>
    intro r h
    simp only [scaleK?, Option.some.injEq] at h
    subst h
    show (0 : A) = φ t.2 * monDenote D ctx nv 0 t.1 * 0
    grind
  | cons t' l ih =>
    intro r h
    simp only [scaleK?] at h
    cases hg : mulKeyOk D nv t.1 t'.1 with
    | false => rw [hg] at h; simp at h
    | true =>
      rw [hg] at h
      simp only [cond_true] at h
      cases hs : scaleK? D nv t l with
      | none => rw [hs] at h; simp at h
      | some r' =>
        rw [hs] at h
        simp only [Option.some.injEq] at h
        subst h
        show φ (t.2 * t'.2) * monDenote D ctx nv 0 (t.1 + t'.1) +
            denote φ ctx D nv r' =
          φ t.2 * monDenote D ctx nv 0 t.1 *
            (φ t'.2 * monDenote D ctx nv 0 t'.1 + denote φ ctx D nv l)
        rw [ih r' hs, hφ.map_mul, monDenote_mul hD ctx hg]
        grind

theorem denote_mulCore? {D : Nat} (hD : 0 < D) (hφ : AlgPoly.IsRingHom φ)
    (nv : Nat) (l₁ l₂ : KPoly C) :
    ∀ r : KPoly C, mulCore? D nv l₁ l₂ = some r →
      denote φ ctx D nv r = denote φ ctx D nv l₁ * denote φ ctx D nv l₂ := by
  induction l₁ with
  | nil =>
    intro r h
    simp only [mulCore?, Option.some.injEq] at h
    subst h
    show (0 : A) = 0 * denote φ ctx D nv l₂
    grind
  | cons t l₁ ih =>
    intro r h
    simp only [mulCore?] at h
    cases hs : scaleK? D nv t l₂ with
    | none => rw [hs] at h; simp at h
    | some s =>
      cases hc : mulCore? D nv l₁ l₂ with
      | none => rw [hs, hc] at h; simp at h
      | some r' =>
        rw [hs, hc] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [denote_addK φ ctx hφ, denote_scaleK? φ ctx hD hφ nv t l₂ s hs, ih r' hc]
        show _ = (φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l₁) *
          denote φ ctx D nv l₂
        grind

theorem denote_mulK? {D : Nat} (hD : 0 < D) (hφ : AlgPoly.IsRingHom φ)
    (nv : Nat) (l₁ l₂ : KPoly C) :
    ∀ r : KPoly C, mulK? D nv l₁ l₂ = some r →
      denote φ ctx D nv r = denote φ ctx D nv l₁ * denote φ ctx D nv l₂ := by
  intro r h
  simp only [mulK?] at h
  cases hb : l₁.length.ble l₂.length with
  | true => rw [hb] at h; exact denote_mulCore? φ ctx hD hφ nv l₁ l₂ r h
  | false =>
    rw [hb] at h
    rw [denote_mulCore? φ ctx hD hφ nv l₂ l₁ r h]
    exact CommSemiring.mul_comm _ _

theorem denote_powK? {D : Nat} (hD : 0 < D) (hφ : AlgPoly.IsRingHom φ)
    (nv : Nat) (l : KPoly C) (k : Nat) :
    ∀ r : KPoly C, powK? D nv l k = some r →
      denote φ ctx D nv r = denote φ ctx D nv l ^ k := by
  induction k with
  | zero =>
    intro r h
    simp only [powK?, Option.some.injEq] at h
    subst h
    show φ 1 * monDenote D ctx nv 0 0 + 0 = denote φ ctx D nv l ^ 0
    rw [hφ.map_one, monDenote_zero, Semiring.pow_zero]
    grind
  | succ k ih =>
    intro r h
    simp only [powK?] at h
    cases hp : powK? D nv l k with
    | none => rw [hp] at h; simp at h
    | some r' =>
      rw [hp] at h
      rw [denote_mulK? φ ctx hD hφ nv l r' r h, ih r' hp, Semiring.pow_succ]
      exact CommSemiring.mul_comm _ _

theorem denote_negK (hφ : AlgPoly.IsRingHom φ) (D nv : Nat) (l : KPoly C) :
    denote φ ctx D nv (negK l) = -denote φ ctx D nv l := by
  induction l with
  | nil =>
    show (0 : A) = -0
    grind
  | cons t l ih =>
    show φ (-t.2) * monDenote D ctx nv 0 t.1 + denote φ ctx D nv (negK l) =
      -(φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l)
    rw [ih, hφ.map_neg]
    grind

theorem denote_canon (hφ : AlgPoly.IsRingHom φ) (D nv : Nat) (l : KPoly C) :
    denote φ ctx D nv (canon l) = denote φ ctx D nv l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [canon]
    cases hz : t.2 == (0 : C) with
    | false =>
      simp only [cond_false]
      show φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv (canon l) =
        φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l
      rw [ih]
    | true =>
      simp only [cond_true]
      have h0 : t.2 = 0 := CoeffRing.beq_sound _ _ hz
      show denote φ ctx D nv (canon l) =
        φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l
      rw [ih, h0, hφ.map_zero]
      grind

theorem beqK_sound : ∀ l₁ l₂ : KPoly C, beqK l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [beqK] at h
  | _ :: _, [], h => by simp [beqK] at h
  | t₁ :: l₁, t₂ :: l₂, h => by
    simp only [beqK, Bool.and_eq_true] at h
    obtain ⟨⟨hk, hc⟩, hl⟩ := h
    have h₁ : t₁.1 = t₂.1 := Nat.eq_of_beq_eq_true hk
    have h₂ : t₁.2 = t₂.2 := CoeffRing.beq_sound _ _ hc
    have ht : t₁ = t₂ := by
      cases t₁; cases t₂
      simp only at h₁ h₂
      rw [h₁, h₂]
    rw [ht, beqK_sound l₁ l₂ hl]

end KPoly

/-! ### Evaluating `AlgExpr` into the packed form -/

namespace AlgExpr

variable {C : Type u} [CoeffRing C]

open KPoly

/-- Evaluate an expression into Kronecker-packed normal form.
`none` when a variable index reaches past `nv` or a monomial product would
overflow a digit — the guards that make the packing sound-by-construction. -/
def toKPoly? (D nv : Nat) : AlgExpr C → Option (KPoly C)
  | .coeff k => some [(0, k)]
  | .var i => bif i.blt nv then some [(D ^ i, 1)] else none
  | .add a b =>
    match a.toKPoly? D nv, b.toKPoly? D nv with
    | some ra, some rb => some (addK ra rb)
    | _, _ => none
  | .mul a b =>
    match a.toKPoly? D nv, b.toKPoly? D nv with
    | some ra, some rb => mulK? D nv ra rb
    | _, _ => none
  | .neg a =>
    match a.toKPoly? D nv with
    | some ra => some (negK ra)
    | none => none
  | .sub a b =>
    match a.toKPoly? D nv, b.toKPoly? D nv with
    | some ra, some rb => some (addK ra (negK rb))
    | _, _ => none
  | .pow a k =>
    match a.toKPoly? D nv with
    | some ra => powK? D nv ra k
    | none => none

variable {A : Type v} [Lean.Grind.CommRing A]

open Lean.Grind

theorem denote_toKPoly? (φ : C → A) (ctx : Context A)
    (hφ : AlgPoly.IsRingHom φ) {D : Nat} (hD : 1 < D) (nv : Nat) (e : AlgExpr C) :
    ∀ r : KPoly C, e.toKPoly? D nv = some r →
      KPoly.denote φ ctx D nv r = e.denote φ ctx := by
  have hD0 : 0 < D := Nat.lt_trans Nat.zero_lt_one hD
  induction e with
  | coeff k =>
    intro r h
    simp only [toKPoly?, Option.some.injEq] at h
    subst h
    show φ k * KPoly.monDenote D ctx nv 0 0 + 0 = φ k
    rw [KPoly.monDenote_zero]
    grind
  | var i =>
    intro r h
    simp only [toKPoly?] at h
    cases hb : i.blt nv with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      have hi : i < nv := Nat.blt_eq.mp hb
      show φ 1 * KPoly.monDenote D ctx nv 0 (D ^ i) + 0 = Var.denote ctx i
      rw [hφ.map_one, KPoly.monDenote_var hD ctx hi 0, Nat.zero_add]
      grind
  | add a b iha ihb =>
    intro r h
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        rw [ha, hb] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [KPoly.denote_addK φ ctx hφ, iha ra ha, ihb rb hb]
        rfl
  | mul a b iha ihb =>
    intro r h
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        rw [ha, hb] at h
        rw [KPoly.denote_mulK? φ ctx hD0 hφ nv ra rb r h, iha ra ha, ihb rb hb]
        rfl
  | neg a iha =>
    intro r h
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      rw [ha] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [KPoly.denote_negK φ ctx hφ, iha ra ha]
      rfl
  | sub a b iha ihb =>
    intro r h
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        rw [ha, hb] at h
        simp only [Option.some.injEq] at h
        subst h
        rw [KPoly.denote_addK φ ctx hφ, KPoly.denote_negK φ ctx hφ, iha ra ha, ihb rb hb]
        show a.denote φ ctx + -b.denote φ ctx = a.denote φ ctx - b.denote φ ctx
        grind
  | pow a k iha =>
    intro r h
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      rw [ha] at h
      rw [KPoly.denote_powK? φ ctx hD0 hφ nv ra k r h, iha ra ha]
      rfl

/-- Bound on every per-variable exponent arising while normalizing `e`;
used by the tactic to pick the Kronecker base `D` (the guards in
`toKPoly?` re-check the choice, so this need not be trusted). -/
def degBound : AlgExpr C → Nat
  | .coeff _ => 0
  | .var _ => 1
  | .add a b => Nat.max a.degBound b.degBound
  | .sub a b => Nat.max a.degBound b.degBound
  | .neg a => a.degBound
  | .mul a b => a.degBound + b.degBound
  | .pow a k => a.degBound * k

/-! ### Linear-combination certificates (cofactors as data)

For ideal-membership goals the certificate is `p = Σ qᵢ·gᵢ + r`, where `p`
and the generators `gᵢ` come from the goal (reified as `AlgExpr`, so their
denotations tie back to the goal by `rfl`), while the cofactors `qᵢ` and the
remainder `r` are produced by Macaulay2.  The cofactors can be enormous
(the `lean4#11861` benchmark has 16024-term quotients) and *never appear in
the goal*, so there is no reason to rebuild them as ring syntax — elaborating
such expressions costs ~1 s per monomial and was the failure mode of the
expression-based pipeline.  Here they stay `KPoly` data: list literals inside
the proof term, touched only by the kernel's evaluation of `checkLinComb`. -/

/-- All generators of the certificate denote to zero (the hypotheses of an
ideal-membership goal).  Proof terms are nested `And.intro`s. -/
def ZeroGens {A : Type v} [Lean.Grind.CommRing A] (φ : C → A)
    (ctx : Context A) : List (KPoly C × AlgExpr C) → Prop
  | [] => True
  | (_, g) :: t => g.denote φ ctx = 0 ∧ ZeroGens φ ctx t

/-- Accumulate `Σ qᵢ · gᵢ` in packed form (cofactors `qᵢ` are already data;
generators `gᵢ` are evaluated from their reified syntax). -/
def sumLinComb? (D nv : Nat) : List (KPoly C × AlgExpr C) → Option (KPoly C)
  | [] => some []
  | (q, g) :: t =>
    match g.toKPoly? D nv, sumLinComb? D nv t with
    | some rg, some acc =>
      match KPoly.mulK? D nv q rg with
      | some qg => some (KPoly.addK qg acc)
      | none => none
    | _, _ => none

/-- The linear-combination certificate check `p = Σ qᵢ·gᵢ + r`, evaluated by
the kernel via `decide`.  As with `checkKEq`, the base `D` and digit count
`nv` are guarded, not trusted. -/
def checkLinComb (D nv : Nat) (p : AlgExpr C) (pairs : List (KPoly C × AlgExpr C))
    (r : KPoly C) : Bool :=
  Nat.blt 1 D &&
    match p.toKPoly? D nv, sumLinComb? D nv pairs with
    | some rp, some acc =>
      KPoly.beqK (KPoly.canon rp) (KPoly.canon (KPoly.addK acc r))
    | _, _ => false

section

variable {A : Type v} [Lean.Grind.CommRing A]

open Lean.Grind

theorem denote_sumLinComb? (φ : C → A) (ctx : Context A)
    (hφ : AlgPoly.IsRingHom φ) {D : Nat} (hD : 1 < D) (nv : Nat)
    (pairs : List (KPoly C × AlgExpr C)) (hz : ZeroGens φ ctx pairs) :
    ∀ acc : KPoly C, sumLinComb? D nv pairs = some acc →
      KPoly.denote φ ctx D nv acc = 0 := by
  have hD0 : 0 < D := Nat.lt_trans Nat.zero_lt_one hD
  induction pairs with
  | nil =>
    intro acc h
    simp only [sumLinComb?, Option.some.injEq] at h
    subst h
    rfl
  | cons qg t ih =>
    obtain ⟨q, g⟩ := qg
    obtain ⟨hg, hzt⟩ := hz
    intro acc h
    simp only [sumLinComb?] at h
    cases hrg : g.toKPoly? D nv with
    | none => rw [hrg] at h; simp at h
    | some rg =>
      cases hacc : sumLinComb? D nv t with
      | none => rw [hrg, hacc] at h; simp at h
      | some accT =>
        simp only [hrg, hacc] at h
        cases hmul : KPoly.mulK? D nv q rg with
        | none => simp [hmul] at h
        | some qgProd =>
          simp only [hmul, Option.some.injEq] at h
          subst h
          rw [KPoly.denote_addK φ ctx hφ,
            KPoly.denote_mulK? φ ctx hD0 hφ nv q rg qgProd hmul,
            denote_toKPoly? φ ctx hφ hD nv g rg hrg, hg, ih hzt accT hacc]
          show KPoly.denote φ ctx D nv q * 0 + 0 = 0
          grind

/--
Soundness of the linear-combination certificate: if the kernel evaluates
`checkLinComb D nv p pairs r` to `true` and every generator denotes to zero,
then `p` denotes to the denotation of the remainder.  For ideal-membership
goals the tactic instantiates `r := []`, whose denotation is definitionally
`0`, closing `p = 0` outright.  The cofactors in `pairs` occur only as data.
-/
theorem eq_of_checkLinComb {C : Type u} {A : Type v}
    [CoeffRing C] [Lean.Grind.CommRing A]
    (φ : C → A) (ctx : Context A) (hφ : AlgPoly.IsRingHom φ)
    (D nv : Nat) (p : AlgExpr C) (pairs : List (KPoly C × AlgExpr C))
    (r : KPoly C) (hz : ZeroGens φ ctx pairs)
    (h : checkLinComb D nv p pairs r = true) :
    p.denote φ ctx = KPoly.denote φ ctx D nv r := by
  simp only [checkLinComb, Bool.and_eq_true] at h
  obtain ⟨hD, h⟩ := h
  have hD : 1 < D := Nat.blt_eq.mp hD
  cases hp : p.toKPoly? D nv with
  | none => rw [hp] at h; simp at h
  | some rp =>
    cases hacc : sumLinComb? D nv pairs with
    | none => rw [hp, hacc] at h; simp at h
    | some acc =>
      rw [hp, hacc] at h
      have hc := KPoly.beqK_sound _ _ h
      have hsum := denote_sumLinComb? φ ctx hφ hD nv pairs hz acc hacc
      rw [← denote_toKPoly? φ ctx hφ hD nv p rp hp,
        ← KPoly.denote_canon φ ctx hφ D nv rp, hc,
        KPoly.denote_canon φ ctx hφ, KPoly.denote_addK φ ctx hφ, hsum]
      show 0 + KPoly.denote φ ctx D nv r = KPoly.denote φ ctx D nv r
      grind

end

/-- The whole certificate check, evaluated by the kernel via `decide`. -/
def checkKEq (D nv : Nat) (e₁ e₂ : AlgExpr C) : Bool :=
  Nat.blt 1 D &&
    match e₁.toKPoly? D nv, e₂.toKPoly? D nv with
    | some r₁, some r₂ => KPoly.beqK (KPoly.canon r₁) (KPoly.canon r₂)
    | _, _ => false

/--
If two expressions have equal Kronecker-packed normal forms — for *any*
choice of base `D` and digit count `nv` accepted by the guards — then they
denote the same value.  This is the packed-form analogue of
`AlgExpr.eq_of_toAlgPoly_eq` and the theorem the tactic's fast path uses.
-/
theorem eq_of_toKPoly_eq {C : Type u} {A : Type v}
    [CoeffRing C] [Lean.Grind.CommRing A]
    (φ : C → A) (ctx : Context A) (hφ : AlgPoly.IsRingHom φ)
    (D nv : Nat) (e₁ e₂ : AlgExpr C)
    (h : checkKEq D nv e₁ e₂ = true) :
    e₁.denote φ ctx = e₂.denote φ ctx := by
  simp only [checkKEq, Bool.and_eq_true] at h
  obtain ⟨hD, h⟩ := h
  have hD : 1 < D := Nat.blt_eq.mp hD
  cases h₁ : e₁.toKPoly? D nv with
  | none => rw [h₁] at h; simp at h
  | some r₁ =>
    cases h₂ : e₂.toKPoly? D nv with
    | none => rw [h₁, h₂] at h; simp at h
    | some r₂ =>
      rw [h₁, h₂] at h
      have hc := KPoly.beqK_sound _ _ h
      rw [← denote_toKPoly? φ ctx hφ hD nv e₁ r₁ h₁,
        ← denote_toKPoly? φ ctx hφ hD nv e₂ r₂ h₂,
        ← KPoly.denote_canon φ ctx hφ D nv r₁,
        ← KPoly.denote_canon φ ctx hφ D nv r₂, hc]

end AlgExpr

end Macaulean

end
