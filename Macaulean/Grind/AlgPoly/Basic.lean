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

## Design

For a polynomial ring tower R₁[x₁,...,xₘ][y₁,...,yₙ]:
- Outer ring: `AlgPoly R` where R = R₁[x₁,...,xₘ], variables are y₁,...,yₙ
- Inner ring R: `AlgPoly Int` (≅ grind's Poly), variables are x₁,...,xₘ

All operations are **total** (no `partial def`) so the kernel can evaluate them
for proof-by-reflection. `combine` uses fuel-based recursion following grind's pattern.

## Denotation

`AlgPoly C` denotes into a ring `A` via a morphism `φ : C → A` and a variable
context `ctx : Var → A`:

  (coeff k).denote φ ctx = φ k
  (add k m p).denote φ ctx = φ k * m.denote ctx + p.denote φ ctx
-/

open Lean.Grind.CommRing (Var Power Mon)

namespace Macaulean

/-- Operations required on coefficients for polynomial normalization. -/
class CoeffRing (C : Type u) extends Zero C, One C, Add C, Mul C, Neg C, BEq C

instance : CoeffRing Int where
  zero := 0; one := 1; add := (· + ·); mul := (· * ·); neg := Int.neg; beq := (· == ·)

/--
Polynomial with coefficients in `C` and variables tracked by `Mon`.
Invariant: terms sorted by grevlex monomial order (descending).
-/
inductive AlgPoly (C : Type u) where
  | coeff (k : C)
  | add (k : C) (v : Mon) (p : AlgPoly C)
  deriving Inhabited, Repr

namespace AlgPoly

variable {C : Type u} [CoeffRing C]

/-- Large fuel value for bounded recursion (same pattern as grind). -/
private def hugeFuel : Nat := 10000

/-! ### Basic constructors -/

def zero : AlgPoly C := .coeff 0
def one : AlgPoly C := .add 1 .unit (.coeff 0)
def ofVar (x : Var) : AlgPoly C := .add 1 (Mon.ofVar x) (.coeff 0)
def ofMon (m : Mon) : AlgPoly C := .add 1 m (.coeff 0)
def ofCoeff (k : C) : AlgPoly C := .coeff k

/-! ### Structurally recursive operations -/

/-- Add a constant to a polynomial (structurally recursive on p). -/
def addCoeff (p : AlgPoly C) (c : C) : AlgPoly C :=
  if c == (0 : C) then p
  else go p
where
  go : AlgPoly C → AlgPoly C
    | .coeff k => .coeff (k + c)
    | .add k m p => .add k m (go p)

/-- Multiply all coefficients by a scalar (structurally recursive on p). -/
def mulCoeff (c : C) (p : AlgPoly C) : AlgPoly C :=
  if c == (0 : C) then .coeff 0
  else if c == (1 : C) then p
  else go p
where
  go : AlgPoly C → AlgPoly C
    | .coeff k => .coeff (c * k)
    | .add k m p => .add (c * k) m (go p)

/-- Insert a term c*m into a sorted polynomial (structurally recursive on p). -/
def insert (c : C) (m : Mon) (p : AlgPoly C) : AlgPoly C :=
  if c == (0 : C) then p
  else if m == Mon.unit then p.addCoeff c
  else go p
where
  go : AlgPoly C → AlgPoly C
    | .coeff k => .add c m (.coeff k)
    | .add k' m' p =>
      match m.grevlex m' with
      | .eq =>
        let k := c + k'
        if k == (0 : C) then p
        else .add k m p
      | .gt => .add c m (.add k' m' p)
      | .lt => .add k' m' (go p)

/-- Concatenate two polynomials without combining like terms. -/
def concat (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  match p₁ with
  | .coeff k => p₂.addCoeff k
  | .add k m p₁ => .add k m (concat p₁ p₂)

/-- Multiply a polynomial by c*m (structurally recursive on p). -/
def mulMon (c : C) (m : Mon) (p : AlgPoly C) : AlgPoly C :=
  if c == (0 : C) then .coeff 0
  else if m == Mon.unit then mulCoeff c p
  else go p
where
  go : AlgPoly C → AlgPoly C
    | .coeff k =>
      if k == (0 : C) then .coeff 0
      else .add (c * k) m (.coeff 0)
    | .add k m' p => .add (c * k) (m.mul m') (go p)

/-! ### Fuel-based combine (addition of sorted polynomials) -/

/-- Add two sorted polynomials. Uses fuel for termination (both args can shrink). -/
def combine (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : AlgPoly C) : AlgPoly C :=
    match fuel with
    | 0 => p₁.concat p₂
    | fuel + 1 => match p₁, p₂ with
      | .coeff k₁, .coeff k₂ => .coeff (k₁ + k₂)
      | .coeff k₁, p₂ => p₂.addCoeff k₁
      | p₁, .coeff k₂ => p₁.addCoeff k₂
      | .add k₁ m₁ p₁, .add k₂ m₂ p₂ =>
        match m₁.grevlex m₂ with
        | .eq =>
          let k := k₁ + k₂
          if k == (0 : C) then go fuel p₁ p₂
          else .add k m₁ (go fuel p₁ p₂)
        | .gt => .add k₁ m₁ (go fuel p₁ (.add k₂ m₂ p₂))
        | .lt => .add k₂ m₂ (go fuel (.add k₁ m₁ p₁) p₂)

/-! ### Multiplication (structurally recursive on p₁) -/

/-- Multiply two polynomials. -/
def mul (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  go p₁ (.coeff 0)
where
  go (p₁ : AlgPoly C) (acc : AlgPoly C) : AlgPoly C :=
    match p₁ with
    | .coeff k => acc.combine (p₂.mulCoeff k)
    | .add k m p₁ => go p₁ (acc.combine (p₂.mulMon k m))

/-! ### Negation, subtraction, exponentiation -/

/-- Negate all coefficients (structurally recursive). -/
def neg : AlgPoly C → AlgPoly C
  | .coeff k => .coeff (-k)
  | .add k m p => .add (-k) m (neg p)

/-- Subtract two polynomials. -/
def sub (p₁ p₂ : AlgPoly C) : AlgPoly C :=
  p₁.combine p₂.neg

/-- Raise to a natural number power (structurally recursive on k). -/
def pow (p : AlgPoly C) : Nat → AlgPoly C
  | 0 => one
  | 1 => p
  | k + 1 => p.mul (pow p k)

/-! ### Equality -/

def beq : AlgPoly C → AlgPoly C → Bool
  | .coeff k₁, .coeff k₂ => k₁ == k₂
  | .add k₁ m₁ p₁, .add k₂ m₂ p₂ => k₁ == k₂ && m₁ == m₂ && beq p₁ p₂
  | _, _ => false

instance : BEq (AlgPoly C) := ⟨beq⟩

/-- A ring homomorphism from C to A. Bundles the properties needed for denotation. -/
structure IsRingHom {A : Type v} [Lean.Grind.Ring A] (φ : C → A) : Prop where
  map_zero : φ 0 = 0
  map_one : φ 1 = 1
  map_add : ∀ a b, φ (a + b) = φ a + φ b
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  map_neg : ∀ a, φ (-a) = -(φ a)

/-! ### Denotation (semantic interpretation) -/

/-- Denote a polynomial into ring A via morphism φ : C → A and variable context. -/
noncomputable def denote {A : Type v} [Lean.Grind.Ring A]
    (φ : C → A) (ctx : Lean.Grind.CommRing.Context A) : AlgPoly C → A
  | .coeff k => φ k
  | .add k m p => φ k * m.denote ctx + denote φ ctx p

/-! ### Grind interop -/

def ofGrindPoly : Lean.Grind.CommRing.Poly → AlgPoly Int
  | .num k => .coeff k
  | .add k m p => .add k m (ofGrindPoly p)

def toGrindPoly : AlgPoly Int → Lean.Grind.CommRing.Poly
  | .coeff k => .num k
  | .add k m p => .add k m (toGrindPoly p)

/-! ### AlgPoly is itself a CoeffRing (enables towers) -/

instance instCoeffRing : CoeffRing (AlgPoly C) where
  zero := .coeff 0
  one := .coeff 1
  add := combine
  mul := mul
  neg := neg
  beq := beq

end AlgPoly

end Macaulean
