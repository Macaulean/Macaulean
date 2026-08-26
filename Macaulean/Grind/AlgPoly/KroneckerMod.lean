/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Macaulean.Grind.AlgPoly.Kronecker
public import Macaulean.Grind.AlgPoly.ModVec
public import Macaulean.Grind.AlgPoly.ModBound

@[expose] public section

/-!
# A GMP-free reflective certificate for polynomial identities

`AlgExpr.eq_of_toKPoly_eq` (in `Kronecker.lean`) proves `e₁ = e₂` by having the
kernel normalize both sides with **exact integer** coefficients.  For the
certificate identities this project cares about, those integers grow to
thousands of bits, so the kernel spends its time inside GMP.  That is a
liability: Lean's Linux binaries shipped GMP 6.1.2, whose `mpn_sec_powm` bug
was exploitable for a proof of `False` (fixed in Lean v4.33.1).  A reflective
certificate whose truth rests on one big bignum computation should not rest on
GMP.

This module replaces the big-integer arithmetic by a **single-pass CRT**: the
same normalization is run once with coefficients in `ModVec ms`, i.e. as a
vector of residues modulo each `mᵢ ∈ ms`, with every `mᵢ` in `[2^30, 2^31)`.
If all residues of every coefficient of `e₁ - e₂` vanish, then every `mᵢ`
divides that coefficient, hence (pairwise coprimality) `∏ mᵢ` does; and an a
priori L1 bound shows the coefficient is smaller in absolute value than
`∏ mᵢ`, so it is zero.

## GMP audit

Every `Nat` and `Int` the kernel computes with on this path stays strictly
below `2^62`, hence inside Lean's boxed-scalar range
(`LEAN_MAX_SMALL_NAT = 2^63 - 1`), hence on the inline scalar fast paths of
`lean.h`.  Concretely, the kernel-evaluated functions are:

| function | values | why bounded |
| --- | --- | --- |
| `KPoly.powNat D i` | `< 2^62` | the tactic checks `D ^ nv < 2^62` natively, computing the power by a multiplication loop, and refuses otherwise |
| `KPoly.mulKeyOk` (`%`, `/`, `+`, `Nat.blt`) | keys `< 2^62` | keys are sums of packed monomial keys, guarded digit-by-digit to stay below `D ^ nv` |
| `KPoly.mergeF`, `scaleK?`, `mulCore?`, `mulK?`, `powK?`, `negK`, `canon` | keys as above; coefficients are `ModVec` | key comparison is `Nat.blt`; `mulK?` compares `List.length` with `Nat.ble` |
| `ModVec.addVals`, `mulVals`, `negVals`, `ofIntVals` | residues `< 2^31`, products `< 2^62` | every `mᵢ < 2^31` (checked: the moduli are literals in the proof term) and each result is reduced by `Int.emod` |
| `ModVec.beqVals`, `KPoly.canon` | residues | `Int.beq` on scalars |
| `UBnd.norm`, `mul`, `add`, `pow`, `shrUp` | mantissas `< 2^31`, so products `< 2^62`; exponents are a few hundred | `UBnd.norm` renormalizes after every operation; `AlgExpr.boundOk` re-checks `m < 2^31` |
| `AlgExpr.ubnd` on a `.coeff k` leaf | `k.natAbs` | the tactic refuses coefficients with `\|k\| ≥ 2^62` |
| `bezOk` | `a * m`, `b * n` with `a, b < 2^31`, `m, n < 2^31` | Bézout witnesses are emitted reduced |
| `allBig`, `boundOk` | literals and small exponents | `Nat.ble`, `Nat.blt` |

Lean-core `Nat`/`Int` operations that appear on the kernel path:
`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble`,
`Nat.blt`, `Nat.decEq`, `Int.add`, `Int.mul`, `Int.neg`, `Int.emod`,
`Int.beq`, `Int.natAbs`.  Each of these has an inline small-scalar
implementation in `include/lean/lean.h`.  **Not** used: `Nat.pow`, `Nat.gcd`,
`Nat.log2`, `Nat.shiftRight`, `Int.gcd`, `Int.pow` — the out-of-line,
GMP-backed primitives.  (`pow2` appears only in the *specification* function
`UBnd.val` and in soundness proofs; the only closed values the kernel ever
reduces it at are `pow2 30` and `pow2 31`, each 30/31 scalar doublings, and
those reductions happen while checking `ModBound.pow2_30`/`pow2_31`, not
during certificate checking.)

Two remarks on scope:

* The key bound `D ^ nv < 2^62` is a *precondition the tactic checks*, not an
  assumption of the soundness theorem: `toKPoly?` guards every key operation
  anyway, so a violated bound could only make the check return `false`.
* The Kronecker packing and the GMP-free coefficient layer are orthogonal.
  Nothing below refers to how monomials are represented; the same `ModVec`
  coefficients and the same L1/CRT argument would work unchanged over
  exponent-vector monomials (`AlgPoly`/`Mon`).
-/

open Lean.Grind.CommRing (Var Power Mon Context)

set_option linter.unusedSectionVars false

namespace Macaulean

/-! ### Re-coefficienting an expression and a packed polynomial -/

namespace AlgExpr

variable {C : Type u} {C' : Type v} [CoeffRing C] [CoeffRing C']

/-- Apply `ρ` to every coefficient of an expression. -/
def mapCoeff (ρ : C → C') : AlgExpr C → AlgExpr C'
  | .coeff k => .coeff (ρ k)
  | .var i => .var i
  | .add a b => .add (a.mapCoeff ρ) (b.mapCoeff ρ)
  | .mul a b => .mul (a.mapCoeff ρ) (b.mapCoeff ρ)
  | .neg a => .neg (a.mapCoeff ρ)
  | .sub a b => .sub (a.mapCoeff ρ) (b.mapCoeff ρ)
  | .pow a k => .pow (a.mapCoeff ρ) k

end AlgExpr

namespace KPoly

variable {C : Type u} {C' : Type v} [CoeffRing C] [CoeffRing C']

/-- Apply `ρ` to every coefficient of a packed polynomial (keys untouched). -/
def mapC (ρ : C → C') (l : KPoly C) : KPoly C' := l.map fun t => (t.1, ρ t.2)

variable {ρ : C → C'}

theorem mapC_nil : mapC ρ ([] : KPoly C) = [] := rfl

theorem mapC_cons (t : Nat × C) (l : KPoly C) :
    mapC ρ (t :: l) = (t.1, ρ t.2) :: mapC ρ l := rfl

theorem mapC_append (l₁ l₂ : KPoly C) :
    mapC ρ (l₁ ++ l₂) = mapC ρ l₁ ++ mapC ρ l₂ := List.map_append

theorem mapC_length (l : KPoly C) : (mapC ρ l).length = l.length := List.length_map _

theorem mapC_mergeF (hρ : CoeffHom ρ) : ∀ (fuel : Nat) (l₁ l₂ : KPoly C),
    mergeF fuel (mapC ρ l₁) (mapC ρ l₂) = mapC ρ (mergeF fuel l₁ l₂)
  | 0, l₁, l₂ => (mapC_append l₁ l₂).symm
  | _ + 1, [], l₂ => rfl
  | _ + 1, _ :: _, [] => rfl
  | fuel + 1, t₁ :: l₁, t₂ :: l₂ => by
    rw [mapC_cons, mapC_cons]
    simp only [mergeF]
    cases hb₁ : t₁.1.blt t₂.1 with
    | true =>
      simp only [cond_true]
      rw [← mapC_cons t₂ l₂, mapC_mergeF hρ fuel l₁ (t₂ :: l₂), mapC_cons]
    | false =>
      simp only [cond_false]
      cases hb₂ : t₂.1.blt t₁.1 with
      | true =>
        simp only [cond_true]
        rw [← mapC_cons t₁ l₁, mapC_mergeF hρ fuel (t₁ :: l₁) l₂, mapC_cons]
      | false =>
        simp only [cond_false]
        rw [mapC_mergeF hρ fuel l₁ l₂, mapC_cons, hρ.map_add]

theorem mapC_addK (hρ : CoeffHom ρ) (l₁ l₂ : KPoly C) :
    addK (mapC ρ l₁) (mapC ρ l₂) = mapC ρ (addK l₁ l₂) :=
  mapC_mergeF hρ mergeFuel l₁ l₂

theorem mapC_scaleK? (hρ : CoeffHom ρ) (D nv : Nat) (t : Nat × C) : ∀ l : KPoly C,
    scaleK? D nv (t.1, ρ t.2) (mapC ρ l) = (scaleK? D nv t l).map (mapC ρ)
  | [] => rfl
  | t' :: l => by
    have ih := mapC_scaleK? hρ D nv t l
    rw [mapC_cons]
    simp only [scaleK?]
    cases hg : mulKeyOk D nv t.1 t'.1 with
    | false => simp
    | true =>
      simp only [cond_true, ih]
      cases hs : scaleK? D nv t l with
      | none => simp
      | some r => simp [mapC_cons, hρ.map_mul]

theorem mapC_mulCore? (hρ : CoeffHom ρ) (D nv : Nat) : ∀ l₁ l₂ : KPoly C,
    mulCore? D nv (mapC ρ l₁) (mapC ρ l₂) = (mulCore? D nv l₁ l₂).map (mapC ρ)
  | [], _ => rfl
  | t :: l₁, l₂ => by
    have h1 := mapC_scaleK? hρ D nv t l₂
    have h2 := mapC_mulCore? hρ D nv l₁ l₂
    rw [mapC_cons]
    simp only [mulCore?, h1, h2]
    cases hs : scaleK? D nv t l₂ with
    | none => simp
    | some s =>
      cases hc : mulCore? D nv l₁ l₂ with
      | none => simp
      | some r => simp [mapC_addK hρ]

theorem mapC_mulK? (hρ : CoeffHom ρ) (D nv : Nat) (l₁ l₂ : KPoly C) :
    mulK? D nv (mapC ρ l₁) (mapC ρ l₂) = (mulK? D nv l₁ l₂).map (mapC ρ) := by
  simp only [mulK?, mapC_length]
  cases hb : l₁.length.ble l₂.length with
  | true =>
    simp only [cond_true]
    exact mapC_mulCore? hρ D nv l₁ l₂
  | false =>
    simp only [cond_false]
    exact mapC_mulCore? hρ D nv l₂ l₁

theorem mapC_powK? (hρ : CoeffHom ρ) (D nv : Nat) (l : KPoly C) : ∀ k : Nat,
    powK? D nv (mapC ρ l) k = (powK? D nv l k).map (mapC ρ)
  | 0 => by simp [powK?, mapC, hρ.map_one]
  | k + 1 => by
    have h1 := mapC_powK? hρ D nv l k
    cases hp : powK? D nv l k with
    | none =>
      rw [hp] at h1
      simp only [powK?, hp, h1]
      simp
    | some r =>
      rw [hp] at h1
      simp only [powK?, hp, h1]
      simp only [Option.map_some]
      exact mapC_mulK? hρ D nv l r

theorem mapC_negK (hρ : CoeffHom ρ) : ∀ l : KPoly C, negK (mapC ρ l) = mapC ρ (negK l)
  | [] => rfl
  | t :: l => by
    have ih := mapC_negK hρ l
    simp only [negK, mapC, List.map_cons] at ih ⊢
    rw [hρ.map_neg]
    simpa using ih

/-- Coefficients whose image under `ρ` survives `canon` are exactly the
nonzero ones, so an empty canonical form means every image is zero. -/
theorem eq_zero_of_canon_mapC (hρ : CoeffHom ρ) : ∀ l : KPoly C,
    canon (mapC ρ l) = [] → ∀ t ∈ l, ρ t.2 = 0
  | [], _, _, hm => by cases hm
  | t :: l, h, t', ht' => by
    rw [mapC_cons] at h
    simp only [canon] at h
    cases hz : (ρ t.2 == (0 : C')) with
    | false => rw [hz] at h; simp at h
    | true =>
      rw [hz] at h
      simp only [cond_true] at h
      cases ht' with
      | head => exact CoeffRing.beq_sound _ _ hz
      | tail _ ht'' => exact eq_zero_of_canon_mapC hρ l h t' ht''

end KPoly

/-! ### Evaluation commutes with re-coefficienting -/

namespace AlgExpr

variable {C : Type u} {C' : Type v} [CoeffRing C] [CoeffRing C'] {ρ : C → C'}

/-- The raw correspondence lemma: `toKPoly?` never inspects a coefficient (all
its guards are about keys and list lengths), so pushing `ρ` through the
expression is the same as pushing it through the result. -/
theorem mapCoeff_toKPoly? (hρ : CoeffHom ρ) (D nv : Nat) : ∀ e : AlgExpr C,
    (e.mapCoeff ρ).toKPoly? D nv = (e.toKPoly? D nv).map (KPoly.mapC ρ)
  | .coeff _ => rfl
  | .var i => by
    show (bif i.blt nv then some [(KPoly.powNat D i, (1 : C'))] else none) =
      Option.map (KPoly.mapC ρ) (bif i.blt nv then some [(KPoly.powNat D i, (1 : C))] else none)
    cases hb : i.blt nv with
    | false => simp
    | true => simp [KPoly.mapC, hρ.map_one]
  | .add a b => by
    show (match (a.mapCoeff ρ).toKPoly? D nv, (b.mapCoeff ρ).toKPoly? D nv with
      | some ra, some rb => some (KPoly.addK ra rb)
      | _, _ => none) = _
    rw [mapCoeff_toKPoly? hρ D nv a, mapCoeff_toKPoly? hρ D nv b]
    cases ha : a.toKPoly? D nv with
    | none => simp [toKPoly?, ha]
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => simp [toKPoly?, ha, hb]
      | some rb => simp [toKPoly?, ha, hb, KPoly.mapC_addK hρ]
  | .sub a b => by
    show (match (a.mapCoeff ρ).toKPoly? D nv, (b.mapCoeff ρ).toKPoly? D nv with
      | some ra, some rb => some (KPoly.addK ra (KPoly.negK rb))
      | _, _ => none) = _
    rw [mapCoeff_toKPoly? hρ D nv a, mapCoeff_toKPoly? hρ D nv b]
    cases ha : a.toKPoly? D nv with
    | none => simp [toKPoly?, ha]
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => simp [toKPoly?, ha, hb]
      | some rb =>
        simp [toKPoly?, ha, hb, KPoly.mapC_negK hρ, KPoly.mapC_addK hρ]
  | .neg a => by
    show (match (a.mapCoeff ρ).toKPoly? D nv with
      | some ra => some (KPoly.negK ra)
      | none => none) = _
    rw [mapCoeff_toKPoly? hρ D nv a]
    cases ha : a.toKPoly? D nv with
    | none => simp [toKPoly?, ha]
    | some ra => simp [toKPoly?, ha, KPoly.mapC_negK hρ]
  | .mul a b => by
    show (match (a.mapCoeff ρ).toKPoly? D nv, (b.mapCoeff ρ).toKPoly? D nv with
      | some ra, some rb => KPoly.mulK? D nv ra rb
      | _, _ => none) = _
    rw [mapCoeff_toKPoly? hρ D nv a, mapCoeff_toKPoly? hρ D nv b]
    cases ha : a.toKPoly? D nv with
    | none => simp [toKPoly?, ha]
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => simp [toKPoly?, ha, hb]
      | some rb => simp [toKPoly?, ha, hb, KPoly.mapC_mulK? hρ]
  | .pow a k => by
    show (match (a.mapCoeff ρ).toKPoly? D nv with
      | some ra => KPoly.powK? D nv ra k
      | none => none) = _
    rw [mapCoeff_toKPoly? hρ D nv a]
    cases ha : a.toKPoly? D nv with
    | none => simp [toKPoly?, ha]
    | some ra => simp [toKPoly?, ha, KPoly.mapC_powK? hρ]

end AlgExpr

/-! ### The `L¹` norm of a packed integer polynomial -/

namespace KPoly

/-- Sum of the absolute values of the coefficients. -/
def l1 : KPoly Int → Nat
  | [] => 0
  | t :: l => t.2.natAbs + l1 l

theorem l1_append : ∀ l₁ l₂ : KPoly Int, l1 (l₁ ++ l₂) = l1 l₁ + l1 l₂
  | [], l₂ => by simp [l1]
  | t :: l₁, l₂ => by
    show t.2.natAbs + l1 (l₁ ++ l₂) = t.2.natAbs + l1 l₁ + l1 l₂
    rw [l1_append l₁ l₂]
    omega

theorem l1_mem : ∀ (l : KPoly Int) (t : Nat × Int), t ∈ l → t.2.natAbs ≤ l1 l
  | [], _, hm => by cases hm
  | t' :: l, t, ht => by
    show _ ≤ t'.2.natAbs + l1 l
    cases ht with
    | head => omega
    | tail _ ht' =>
      have := l1_mem l t ht'
      omega

theorem l1_mergeF : ∀ (fuel : Nat) (l₁ l₂ : KPoly Int),
    l1 (mergeF fuel l₁ l₂) ≤ l1 l₁ + l1 l₂
  | 0, l₁, l₂ => Nat.le_of_eq (l1_append l₁ l₂)
  | _ + 1, [], l₂ => by simp [mergeF, l1]
  | _ + 1, t :: l₁, [] => by simp [mergeF, l1]
  | fuel + 1, t₁ :: l₁, t₂ :: l₂ => by
    simp only [mergeF]
    cases hb₁ : t₁.1.blt t₂.1 with
    | true =>
      have h := l1_mergeF fuel l₁ (t₂ :: l₂)
      simp only [cond_true, l1] at h ⊢
      omega
    | false =>
      simp only [cond_false]
      cases hb₂ : t₂.1.blt t₁.1 with
      | true =>
        have h := l1_mergeF fuel (t₁ :: l₁) l₂
        simp only [cond_true, l1] at h ⊢
        omega
      | false =>
        have h := l1_mergeF fuel l₁ l₂
        have hab : (t₁.2 + t₂.2).natAbs ≤ t₁.2.natAbs + t₂.2.natAbs :=
          Int.natAbs_add_le _ _
        simp only [cond_false, l1] at h ⊢
        omega

theorem l1_addK (l₁ l₂ : KPoly Int) : l1 (addK l₁ l₂) ≤ l1 l₁ + l1 l₂ :=
  l1_mergeF mergeFuel l₁ l₂

theorem l1_scaleK? (D nv : Nat) (t : Nat × Int) : ∀ (l r : KPoly Int),
    scaleK? D nv t l = some r → l1 r ≤ t.2.natAbs * l1 l
  | [], r, h => by
    simp only [scaleK?, Option.some.injEq] at h
    subst h
    simp [l1]
  | t' :: l, r, h => by
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
        have ih := l1_scaleK? D nv t l r' hs
        have hm : (t.2 * t'.2).natAbs = t.2.natAbs * t'.2.natAbs := Int.natAbs_mul _ _
        show (t.2 * t'.2).natAbs + l1 r' ≤ t.2.natAbs * (t'.2.natAbs + l1 l)
        rw [hm, Nat.mul_add]
        omega

theorem l1_mulCore? (D nv : Nat) : ∀ (l₁ l₂ r : KPoly Int),
    mulCore? D nv l₁ l₂ = some r → l1 r ≤ l1 l₁ * l1 l₂
  | [], _, r, h => by
    simp only [mulCore?, Option.some.injEq] at h
    subst h
    simp [l1]
  | t :: l₁, l₂, r, h => by
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
        have h1 := l1_addK s r'
        have h2 := l1_scaleK? D nv t l₂ s hs
        have h3 := l1_mulCore? D nv l₁ l₂ r' hc
        show l1 (addK s r') ≤ (t.2.natAbs + l1 l₁) * l1 l₂
        rw [Nat.add_mul]
        omega

theorem l1_mulK? (D nv : Nat) (l₁ l₂ r : KPoly Int)
    (h : mulK? D nv l₁ l₂ = some r) : l1 r ≤ l1 l₁ * l1 l₂ := by
  simp only [mulK?] at h
  cases hb : l₁.length.ble l₂.length with
  | true =>
    rw [hb] at h
    exact l1_mulCore? D nv l₁ l₂ r h
  | false =>
    rw [hb] at h
    have := l1_mulCore? D nv l₂ l₁ r h
    rw [Nat.mul_comm] at this
    exact this

theorem l1_powK? (D nv : Nat) (l : KPoly Int) : ∀ (k : Nat) (r : KPoly Int),
    powK? D nv l k = some r → l1 r ≤ (l1 l) ^ k
  | 0, r, h => by
    simp only [powK?, Option.some.injEq] at h
    subst h
    show (1 : Int).natAbs + 0 ≤ (l1 l) ^ 0
    simp
  | k + 1, r, h => by
    simp only [powK?] at h
    cases hp : powK? D nv l k with
    | none => rw [hp] at h; simp at h
    | some r' =>
      rw [hp] at h
      have h1 := l1_mulK? D nv l r' r h
      have h2 := l1_powK? D nv l k r' hp
      have h3 : l1 l * l1 r' ≤ l1 l * (l1 l) ^ k :=
        Nat.mul_le_mul (Nat.le_refl _) h2
      rw [Nat.pow_succ, Nat.mul_comm ((l1 l) ^ k) (l1 l)]
      omega

theorem l1_negK : ∀ l : KPoly Int, l1 (negK l) = l1 l
  | [] => rfl
  | t :: l => by
    show (-t.2).natAbs + l1 (negK l) = t.2.natAbs + l1 l
    rw [l1_negK l, Int.natAbs_neg]

end KPoly

/-! ### An a priori `L¹` bound for an expression -/

namespace AlgExpr

/-- The mathematical L1 bound.  **Never** evaluated by the kernel: it is a
tower of exact products and can be astronomically large. -/
def l1Bound : AlgExpr Int → Nat
  | .coeff k => k.natAbs
  | .var _ => 1
  | .add a b => a.l1Bound + b.l1Bound
  | .sub a b => a.l1Bound + b.l1Bound
  | .neg a => a.l1Bound
  | .mul a b => a.l1Bound * b.l1Bound
  | .pow a k => a.l1Bound ^ k

theorem l1_toKPoly? (D nv : Nat) : ∀ (e : AlgExpr Int) (l : KPoly Int),
    e.toKPoly? D nv = some l → KPoly.l1 l ≤ e.l1Bound
  | .coeff k, l, h => by
    simp only [toKPoly?, Option.some.injEq] at h
    subst h
    show k.natAbs + 0 ≤ k.natAbs
    omega
  | .var i, l, h => by
    simp only [toKPoly?] at h
    cases hb : i.blt nv with
    | false => rw [hb] at h; simp at h
    | true =>
      rw [hb] at h
      simp only [cond_true, Option.some.injEq] at h
      subst h
      show (1 : Int).natAbs + 0 ≤ 1
      simp
  | .add a b, l, h => by
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
        have h1 := KPoly.l1_addK ra rb
        have h2 := l1_toKPoly? D nv a ra ha
        have h3 := l1_toKPoly? D nv b rb hb
        show KPoly.l1 (KPoly.addK ra rb) ≤ a.l1Bound + b.l1Bound
        omega
  | .sub a b, l, h => by
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
        have h1 := KPoly.l1_addK ra (KPoly.negK rb)
        have h2 := l1_toKPoly? D nv a ra ha
        have h3 := l1_toKPoly? D nv b rb hb
        have h4 := KPoly.l1_negK rb
        show KPoly.l1 (KPoly.addK ra (KPoly.negK rb)) ≤ a.l1Bound + b.l1Bound
        omega
  | .neg a, l, h => by
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      rw [ha] at h
      simp only [Option.some.injEq] at h
      subst h
      have h2 := l1_toKPoly? D nv a ra ha
      have h4 := KPoly.l1_negK ra
      show KPoly.l1 (KPoly.negK ra) ≤ a.l1Bound
      omega
  | .mul a b, l, h => by
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      cases hb : b.toKPoly? D nv with
      | none => rw [ha, hb] at h; simp at h
      | some rb =>
        rw [ha, hb] at h
        have h1 := KPoly.l1_mulK? D nv ra rb l h
        have h2 := l1_toKPoly? D nv a ra ha
        have h3 := l1_toKPoly? D nv b rb hb
        exact Nat.le_trans h1 (Nat.mul_le_mul h2 h3)
  | .pow a k, l, h => by
    simp only [toKPoly?] at h
    cases ha : a.toKPoly? D nv with
    | none => rw [ha] at h; simp at h
    | some ra =>
      rw [ha] at h
      have h1 := KPoly.l1_powK? D nv ra k l h
      have h2 := l1_toKPoly? D nv a ra ha
      exact Nat.le_trans h1 (Nat.pow_le_pow_left h2 k)

/-- A kernel-computable upper bound for `l1Bound`, as a mantissa/exponent
pair.  Every mantissa stays below `2^31`. -/
def ubnd : AlgExpr Int → UBnd
  | .coeff k => UBnd.ofNat k.natAbs
  | .var _ => ⟨1, 0⟩
  | .add a b => UBnd.add a.ubnd b.ubnd
  | .sub a b => UBnd.add a.ubnd b.ubnd
  | .neg a => a.ubnd
  | .mul a b => UBnd.mul a.ubnd b.ubnd
  | .pow a k => UBnd.pow a.ubnd k

theorem l1Bound_le_ubnd : ∀ e : AlgExpr Int, e.l1Bound ≤ e.ubnd.val
  | .coeff k => UBnd.le_ofNat _
  | .var _ => Nat.le_refl 1
  | .add a b => Nat.le_trans (Nat.add_le_add (l1Bound_le_ubnd a) (l1Bound_le_ubnd b))
      (UBnd.le_add _ _)
  | .sub a b => Nat.le_trans (Nat.add_le_add (l1Bound_le_ubnd a) (l1Bound_le_ubnd b))
      (UBnd.le_add _ _)
  | .neg a => l1Bound_le_ubnd a
  | .mul a b => Nat.le_trans (Nat.mul_le_mul (l1Bound_le_ubnd a) (l1Bound_le_ubnd b))
      (UBnd.le_mul _ _)
  | .pow a k => Nat.le_trans (Nat.pow_le_pow_left (l1Bound_le_ubnd a) k)
      (UBnd.le_pow _ k)

end AlgExpr

/-! ### The kernel-side checks -/

/-- `true` on the empty list. -/
def isNilB {α : Type u} : List α → Bool
  | [] => true
  | _ :: _ => false

theorem eq_nil_of_isNilB {α : Type u} : ∀ l : List α, isNilB l = true → l = []
  | [], _ => rfl
  | _ :: _, h => by simp [isNilB] at h

namespace AlgExpr

/-- Normalize `e` with residue-vector coefficients and check that every
coefficient of the result vanishes modulo every modulus.  Kernel-evaluated. -/
def checkModZero (D nv : Nat) (ms : List Nat) (e : AlgExpr Int) : Bool :=
  Nat.blt 1 D &&
    match (e.mapCoeff (ModVec.ofInt ms)).toKPoly? D nv with
    | some l => isNilB (KPoly.canon l)
    | none => false

/-- Check that the a priori L1 bound for `e` is below `∏ ms`, using only
comparisons of small `Nat`s.  Kernel-evaluated. -/
def boundOk (ms : List Nat) (e : AlgExpr Int) : Bool :=
  Nat.ble (31 + e.ubnd.e) (30 * ms.length) && Nat.blt e.ubnd.m 2147483648

end AlgExpr

namespace KPoly

variable {A : Type v} [Lean.Grind.CommRing A]

open Lean.Grind

theorem denote_eq_zero (φ : Int → A) (ctx : Context A) (hφ : AlgPoly.IsRingHom φ)
    (D nv : Nat) : ∀ l : KPoly Int, (∀ t ∈ l, t.2 = 0) → denote φ ctx D nv l = 0
  | [], _ => rfl
  | t :: l, h => by
    show φ t.2 * monDenote D ctx nv 0 t.1 + denote φ ctx D nv l = 0
    rw [h t (List.Mem.head _), hφ.map_zero,
      denote_eq_zero φ ctx hφ D nv l fun x hx => h x (List.Mem.tail _ hx)]
    grind

end KPoly

/-! ### Soundness of the GMP-free certificate -/

namespace AlgExpr

variable {A : Type v} [Lean.Grind.CommRing A]

open Lean.Grind

/--
The single-pass-CRT certificate.

If

* `ms` is certified pairwise coprime by the Bézout table `tbl`,
* every modulus in `ms` is at least `2^30`,
* normalizing `e₁ - e₂` with coefficients in `ModVec ms` gives the zero
  polynomial, and
* the a priori `L¹` bound for `e₁ - e₂` is below `2^(30 * ms.length) ≤ ∏ ms`,

then `e₁` and `e₂` denote the same element of `A`.

Only the first four hypotheses are checked, all four by `Bool` evaluation on
values below `2^62`; a wrong choice of `D`, `nv` or `ms` can only make a check
return `false`.
-/
theorem eq_of_checkModZero
    (φ : Int → A) (ctx : Context A) (hφ : AlgPoly.IsRingHom φ)
    (D nv : Nat) (ms : List Nat) (tbl : List (List (Nat × Nat)))
    (e₁ e₂ : AlgExpr Int)
    (hcop : pairwiseCoprimeB ms tbl = true)
    (hbig : allBig ms = true)
    (hchk : checkModZero D nv ms (e₁.sub e₂) = true)
    (hbnd : boundOk ms (e₁.sub e₂) = true) :
    e₁.denote φ ctx = e₂.denote φ ctx := by
  have hρ := ModVec.ofInt_isCoeffHom ms
  simp only [checkModZero, Bool.and_eq_true] at hchk
  obtain ⟨hD, hchk⟩ := hchk
  have hD : 1 < D := Nat.blt_eq.mp hD
  simp only [boundOk, Bool.and_eq_true] at hbnd
  obtain ⟨hbe, hbm⟩ := hbnd
  have hbe : 31 + (e₁.sub e₂).ubnd.e ≤ 30 * ms.length := Nat.ble_eq.mp hbe
  have hbm : (e₁.sub e₂).ubnd.m < 2147483648 := Nat.blt_eq.mp hbm
  rw [mapCoeff_toKPoly? hρ D nv (e₁.sub e₂)] at hchk
  cases hl : (e₁.sub e₂).toKPoly? D nv with
  | none => rw [hl] at hchk; simp at hchk
  | some l =>
    rw [hl] at hchk
    simp only [Option.map_some] at hchk
    have hcanon : KPoly.canon (KPoly.mapC (ModVec.ofInt ms) l) = [] :=
      eq_nil_of_isNilB _ hchk
    -- every coefficient of `l` is smaller than `∏ ms`
    have hlt : ∀ t ∈ l, t.2.natAbs < prodN ms := by
      intro t ht
      have b1 : t.2.natAbs ≤ KPoly.l1 l := KPoly.l1_mem l t ht
      have b2 : KPoly.l1 l ≤ (e₁.sub e₂).l1Bound := l1_toKPoly? D nv _ l hl
      have b3 : (e₁.sub e₂).l1Bound ≤ (e₁.sub e₂).ubnd.val := l1Bound_le_ubnd _
      have b4 : (e₁.sub e₂).ubnd.val < pow2 (31 + (e₁.sub e₂).ubnd.e) :=
        UBnd.val_lt _ hbm
      have b5 : pow2 (31 + (e₁.sub e₂).ubnd.e) ≤ pow2 (30 * ms.length) :=
        pow2_le_pow2 hbe
      have b6 : pow2 (30 * ms.length) ≤ prodN ms := pow2_le_prodN ms hbig
      omega
    -- every coefficient of `l` vanishes
    have hzero : ∀ t ∈ l, t.2 = 0 := by
      intro t ht
      have hr : ModVec.ofInt ms t.2 = 0 :=
        KPoly.eq_zero_of_canon_mapC hρ l hcanon t ht
      have hdvd : ∀ m ∈ ms, (m : Int) ∣ t.2 := ModVec.dvd_of_ofInt_eq_zero hr
      have hdvdN : ∀ m ∈ ms, m ∣ t.2.natAbs := by
        intro m hm
        have := Int.natAbs_dvd_natAbs.mpr (hdvd m hm)
        rwa [Int.natAbs_natCast] at this
      have hprod : prodN ms ∣ t.2.natAbs :=
        prodN_dvd ms (pairwiseCoprimeB_sound ms tbl hcop) hdvdN
      have hz : t.2.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hprod (hlt t ht)
      exact Int.natAbs_eq_zero.mp hz
    have hden : KPoly.denote φ ctx D nv l = 0 :=
      KPoly.denote_eq_zero φ ctx hφ D nv l hzero
    rw [denote_toKPoly? φ ctx hφ hD nv (e₁.sub e₂) l hl] at hden
    show e₁.denote φ ctx = e₂.denote φ ctx
    have : e₁.denote φ ctx - e₂.denote φ ctx = 0 := hden
    grind

end AlgExpr

/-! ### The canonical `Int → A` map is a coefficient morphism -/

/-- The canonical coefficient map `Int → A`.

`Lean.Grind.CommRing.denoteInt` is grind's own canonical map: an `abbrev` that
produces `OfNat.ofNat |k|` (negated when `k < 0`) using grind's numeral
instance, which is what makes the tactic's denotation bridge reduce to the
goal's own numerals.  Packaging
it as a named definition (rather than letting the tactic build the `denoteInt`
application itself) keeps the `Lean.Grind.Ring` instance argument in one place,
so the term the tactic emits and the term `intDenote_isRingHom` talks about are
syntactically identical. -/
noncomputable def intDenote (A : Type v) [Lean.Grind.CommRing A] : Int → A :=
  fun k => Lean.Grind.CommRing.denoteInt k

theorem intDenote_isRingHom (A : Type v) [Lean.Grind.CommRing A] :
    AlgPoly.IsRingHom (intDenote A) where
  map_zero := by
    simp only [intDenote, Lean.Grind.CommRing.denoteInt_eq]
    exact Lean.Grind.Ring.intCast_zero
  map_one := by
    simp only [intDenote, Lean.Grind.CommRing.denoteInt_eq]
    exact Lean.Grind.Ring.intCast_one
  map_add a b := by
    simp only [intDenote, Lean.Grind.CommRing.denoteInt_eq]
    exact Lean.Grind.Ring.intCast_add a b
  map_mul a b := by
    simp only [intDenote, Lean.Grind.CommRing.denoteInt_eq]
    exact Lean.Grind.Ring.intCast_mul a b
  map_neg a := by
    simp only [intDenote, Lean.Grind.CommRing.denoteInt_eq]
    exact Lean.Grind.Ring.intCast_neg a

end Macaulean

end
