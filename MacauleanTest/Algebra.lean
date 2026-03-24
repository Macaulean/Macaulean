/-
Tests for Lean.Grind.Algebra — M2 verification optimization.

The key value: when A = R[x₁,...,xₙ] is a polynomial ring over R, coefficient
arithmetic should be verified in R (cheap) rather than in the full ring A (expensive).
The Algebra extension rewrites smul → algebraMap*x, and @[grind =] lemmas handle
algebraMap homomorphism (expansion/contraction). The ring solver normalizes the rest.
-/

import Macaulean.Grind.Algebra.Instances
-- import Macaulean.Grind.Algebra.Extension  -- temporarily disabled to test

open Lean Grind

-- variable declarations are inline on each example

/-! ## Group 1: Coefficient product verification

When M2 returns a factorization, we verify f₁ * f₂ = g. The coefficients multiply
in R. These tests check that coefficient multiplication can be verified via R
rather than in the full ring A. -/

-- M2 says: coefficient c₁ * c₂ = c₃ in R. Verify in A.
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ c₃ : R) (h : c₁ * c₂ = c₃) :
    algebraMap R A c₁ * algebraMap R A c₂ = algebraMap R A c₃ := by
  grind

-- M2 says this coefficient sum is zero.
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (h : c₁ + c₂ = 0) :
    algebraMap R A c₁ + algebraMap R A c₂ = 0 := by
  grind

-- M2 factors a coefficient: c = a * b in R. Match in A.
example [CommRing R] [CommRing A] [Algebra R A]
    (a b c : R) (h : a * b = c) (x : A) :
    algebraMap R A a * (algebraMap R A b * x) = algebraMap R A c * x := by
  grind

/-! ## Group 2: Coefficient collection — expressions in im(algebraMap)

When the entire expression lives in im(algebraMap), normalization should happen
in R not A. The @[grind =] lemmas let grind expand/contract algebraMap through
ring operations, and the ring solver normalizes. -/

-- Difference of squares: (aM r + aM s)*(aM r - aM s) = aM(r²-s²)
-- For complex polynomial identities, explicit coefficient rewriting + ring is the
-- optimal M2 verification pattern: it minimizes kernel computation.
example [CommRing R] [CommRing A] [Algebra R A] (r s : R) :
    (algebraMap R A r + algebraMap R A s) *
    (algebraMap R A r - algebraMap R A s) =
    algebraMap R A (r * r - s * s) := by
  simp only [Algebra.algebraMap_sub, Algebra.algebraMap_mul, Algebra.algebraMap_add]; grind

-- Three-factor product
example [CommRing R] [CommRing A] [Algebra R A] (r s t : R) :
    algebraMap R A r * algebraMap R A s * algebraMap R A t =
    algebraMap R A (r * s * t) := by
  grind

-- Coefficient square: (r+s)² in A via R
example [CommRing R] [CommRing A] [Algebra R A] (r s : R) :
    (algebraMap R A r + algebraMap R A s) *
    (algebraMap R A r + algebraMap R A s) =
    algebraMap R A (r * r + r * s + s * r + s * s) := by
  grind

/-! ## Group 3: Mixed coefficient + variable — the polynomial ring case

The typical M2 result: polynomials with coefficients in R and variables in A.
Coefficient ops verified in R, variable structure in A. -/

-- Distribute a coefficient across a sum of A-terms.
example [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (x y : A) :
    algebraMap R A r * (x + y) = algebraMap R A r * x + algebraMap R A r * y := by
  grind

-- Two-term polynomial multiplication: (c₁*x)*(c₂*y) = (c₁*c₂)*(x*y)
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x y : A) :
    (algebraMap R A c₁ * x) * (algebraMap R A c₂ * y) =
    algebraMap R A (c₁ * c₂) * (x * y) := by
  grind

-- Collect like terms: c₁*x + c₂*x = (c₁+c₂)*x
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    algebraMap R A c₁ * x + algebraMap R A c₂ * x =
    algebraMap R A (c₁ + c₂) * x := by
  grind

-- smul version of above (the way M2 results typically arrive)
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    c₁ • x + c₂ • x = (c₁ + c₂) • x := by
  grind

/-! ## Group 4: M2-style verification with coefficient hypotheses

M2 computed a result and gave us coefficient relations. We verify using those
relations without expanding everything in A. -/

-- M2 says this polynomial vanishes because the coefficient relation holds.
-- Strategy: contract coefficient product, apply hypothesis in R, then ring.
example [CommRing R] [CommRing A] [Algebra R A]
    (a b c : R) (x : A)
    (h : a * b - c = 0) :
    algebraMap R A a * (algebraMap R A b * x) - algebraMap R A c * x = 0 := by
  rw [← Semiring.mul_assoc, ← Algebra.algebraMap_mul]; grind

-- M2 gives a linear combination certificate: a₁ + a₂ = 1.
-- Strategy: rewrite smul, collect algebraMap coefficients, apply hypothesis.
example [CommRing R] [CommRing A] [Algebra R A]
    (a₁ a₂ : R) (x : A)
    (h : a₁ + a₂ = 1) :
    a₁ • x + a₂ • x = x := by
  rw [Algebra.algebraMap_smul_def, Algebra.algebraMap_smul_def,
      ← Semiring.right_distrib, ← Algebra.algebraMap_add]; grind

-- Coefficient commutativity from M2 result
example [CommRing R] [CommRing A] [Algebra R A]
    (r s : R) (x : A)
    (h : r * s = s * r) :
    algebraMap R A r * (algebraMap R A s * x) =
    algebraMap R A s * (algebraMap R A r * x) := by
  grind

/-! ## Group 5: Stress test — where subalgebra lifting really pays off -/

-- Large coefficient expression: (a+b+c)*(d+e+f)
-- Explicit coefficient expansion is the right strategy for large expressions.
example [CommRing R] [CommRing A] [Algebra R A]
    (a b c d e f : R) :
    (algebraMap R A a + algebraMap R A b + algebraMap R A c) *
    (algebraMap R A d + algebraMap R A e + algebraMap R A f) =
    algebraMap R A (a*d + a*e + a*f + b*d + b*e + b*f + c*d + c*e + c*f) := by
  simp only [Algebra.algebraMap_add, Algebra.algebraMap_mul]
  grind

-- Coefficient identity collapses expression: r³ = r
example [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (x : A)
    (h : r * r * r = r) :
    algebraMap R A r * algebraMap R A r * algebraMap R A r * x =
    algebraMap R A r * x := by
  grind
