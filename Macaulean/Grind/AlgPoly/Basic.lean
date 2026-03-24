/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean

/-!
# AlgPoly: Polynomials with parameterized coefficients

A polynomial type `AlgPoly C` with coefficients in a ring `C`, reusing grind's
monomial representation (`Mon`, `Power`, `Var`). This generalizes `Lean.Grind.CommRing.Poly`
(which hardcodes `Int` coefficients) to support algebra-aware normalization.

## Key idea

For a polynomial ring tower R₁[x₁,...,xₘ][y₁,...,yₙ]:
- Outer ring: `AlgPoly R` where R = R₁[x₁,...,xₘ], variables are y₁,...,yₙ
- Inner ring R: `AlgPoly Int` (= grind's Poly), variables are x₁,...,xₘ

Verification of `Σ aᵢ*gᵢ = f` does polynomial ops in y (few variables, fast)
with coefficient ops delegated to R (separate, possibly recursive).

## Denotation

`AlgPoly C` denotes into a ring `A` via a morphism `φ : C → A` and a variable
context `ctx : Var → A`:

  (coeff k).denote φ ctx = φ k
  (add k m p).denote φ ctx = φ k * m.denote ctx + p.denote φ ctx

When `φ = algebraMap R A`, this gives the algebra interpretation.
-/

open Lean.Grind.CommRing (Var Power Mon)

namespace Macaulean

/--
A polynomial with coefficients in `C` and variables tracked by `Mon`.
Sorted by grevlex monomial order (same invariant as `Grind.CommRing.Poly`).

`AlgPoly C` generalizes `Grind.CommRing.Poly` which is effectively `AlgPoly Int`.
-/
inductive AlgPoly (C : Type u) where
  /-- A constant (no variables). -/
  | coeff (k : C)
  /-- `k * v + p` where `k` is a coefficient, `v` is a monomial, `p` is the rest. -/
  | add (k : C) (v : Mon) (p : AlgPoly C)
  deriving Inhabited, Repr

namespace AlgPoly

variable {C : Type u}

/-!
### Coefficient requirements

We use `CoeffRing` as a bundle of the operations needed on coefficients.
This avoids threading many typeclass arguments through every function.
-/

/-- The operations required on coefficients for polynomial normalization. -/
class CoeffRing (C : Type u) extends Zero C, One C, Add C, Mul C, Neg C, BEq C

instance : CoeffRing Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := Int.neg
  beq := (· == ·)

variable [CoeffRing C]

/-! ### Structural operations -/

/-- The zero polynomial. -/
def zero : AlgPoly C := .coeff 0

/-- A single variable as a polynomial: 1 * x^1. -/
def ofVar (x : Var) : AlgPoly C :=
  .add 1 (Mon.ofVar x) (.coeff 0)

/-- A single monomial with coefficient 1. -/
def ofMon (m : Mon) : AlgPoly C :=
  .add 1 m (.coeff 0)

/-- A constant polynomial. -/
def ofCoeff (k : C) : AlgPoly C := .coeff k

/-! ### Coefficient scaling -/

/-- Multiply all coefficients by a scalar. -/
def mulCoeff (c : C) (p : AlgPoly C) : AlgPoly C :=
  if c == (0 : C) then .coeff 0
  else if c == (1 : C) then p
  else go p
where
  go : AlgPoly C → AlgPoly C
    | .coeff k => .coeff (c * k)
    | .add k m p => .add (c * k) m (go p)

/-! ### Addition (merging sorted polynomials) -/

/-- Add a constant to a polynomial. -/
def addCoeff (p : AlgPoly C) (c : C) : AlgPoly C :=
  match p with
  | .coeff k => .coeff (k + c)
  | .add k m p => .add k m (addCoeff p c)

/-- Insert a term `c * m` into a sorted polynomial. -/
partial def insert (c : C) (m : Mon) (p : AlgPoly C) : AlgPoly C :=
  match p with
  | .coeff k =>
    if c == (0 : C) then .coeff k
    else .add c m (.coeff k)
  | .add k' m' p' =>
    match m.grevlex m' with
    | .eq =>
      let k := c + k'
      if k == (0 : C) then p'
      else .add k m' p'
    | .gt => .add c m (.add k' m' p')
    | .lt => .add k' m' (insert c m p')

/-- Add two sorted polynomials. -/
partial def combine (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  match p₁, p₂ with
  | .coeff k₁, .coeff k₂ => .coeff (k₁ + k₂)
  | .coeff k₁, p₂ => addCoeff p₂ k₁
  | p₁, .coeff k₂ => addCoeff p₁ k₂
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
    match m₁.grevlex m₂ with
    | .eq =>
      let k := k₁ + k₂
      if k == (0 : C) then combine p₁ p₂
      else .add k m₁ (combine p₁ p₂)
    | .gt => .add k₁ m₁ (combine p₁ (.add k₂ m₂ p₂))
    | .lt => .add k₂ m₂ (combine (.add k₁ m₁ p₁) p₂)

/-! ### Monomial multiplication -/

/-- Multiply a polynomial by `c * m` (a single term). -/
partial def mulMon (c : C) (m : Mon) (p : AlgPoly C) : AlgPoly C :=
  if c == (0 : C) then .coeff 0
  else if m == Mon.unit then mulCoeff c p
  else go p
where
  go : AlgPoly C → AlgPoly C
    | .coeff k =>
      if k == (0 : C) then .coeff 0
      else .add (c * k) m (.coeff 0)
    | .add k m' p => .add (c * k) (m.mul m') (go p)

/-! ### Polynomial multiplication -/

/-- Multiply two polynomials. -/
partial def mul (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  go p₁ (.coeff 0)
where
  go (p₁ : AlgPoly C) (acc : AlgPoly C) : AlgPoly C :=
    match p₁ with
    | .coeff k => acc.combine (p₂.mulCoeff k)
    | .add k m p₁ => go p₁ (acc.combine (p₂.mulMon k m))

/-! ### Negation and subtraction -/

/-- Negate all coefficients. -/
def neg : AlgPoly C → AlgPoly C
  | .coeff k => .coeff (-k)
  | .add k m p => .add (-k) m (neg p)

/-- Subtract two polynomials. -/
def sub (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  p₁.combine p₂.neg

/-! ### Exponentiation -/

/-- Raise a polynomial to a natural number power. -/
def pow (p : AlgPoly C) : Nat → AlgPoly C
  | 0 => .add 1 Mon.unit (.coeff 0)  -- 1
  | 1 => p
  | n + 1 => p.mul (pow p n)

/-! ### Equality checking -/

/-- Decidable equality for AlgPoly (given decidable equality on C). -/
def beq : AlgPoly C → AlgPoly C → Bool
  | .coeff k₁, .coeff k₂ => k₁ == k₂
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ => k₁ == k₂ && m₁ == m₂ && beq p₁ p₂
  | _, _ => false

instance : BEq (AlgPoly C) := ⟨beq⟩

/-! ### Denotation -/

/--
Denote a polynomial into a ring `A` via:
- `φ : C → A` — the coefficient morphism (e.g., algebraMap R A)
- `ctx : Lean.Grind.CommRing.Context A` — variable assignments

This is the semantic interpretation used for proof-by-reflection.
-/
noncomputable def denote {A : Type v} [Lean.Grind.Ring A]
    (φ : C → A) (ctx : Lean.Grind.CommRing.Context A) : AlgPoly C → A
  | .coeff k => φ k
  | .add k m p => φ k * m.denote ctx + denote φ ctx p

/-! ### Conversion from/to Grind.CommRing.Poly -/

/-- Convert from grind's Poly (Int coefficients) to AlgPoly Int. -/
def ofGrindPoly : Lean.Grind.CommRing.Poly → AlgPoly Int
  | .num k => .coeff k
  | .add k m p => .add k m (ofGrindPoly p)

/-- Convert to grind's Poly (only works for Int coefficients). -/
def toGrindPoly : AlgPoly Int → Lean.Grind.CommRing.Poly
  | .coeff k => .num k
  | .add k m p => .add k m (toGrindPoly p)

/-! ### AlgPoly is itself a CoeffRing (enables towers) -/

/--
`AlgPoly C` forms a `CoeffRing`, so it can be used as the coefficient type
for an outer polynomial ring. This gives us towers:
`AlgPoly (AlgPoly Int)` = polynomials over polynomials over ℤ.
-/
instance instCoeffRing : CoeffRing (AlgPoly C) where
  zero := .coeff 0
  one := .coeff 1
  add := combine
  mul := mul
  neg := neg
  beq := beq

end AlgPoly

end Macaulean
