/-
Tests for Lean.Grind.Algebra — M2 verification optimization.

The key value: when A = R[x₁,...,xₙ] is a polynomial ring over R, coefficient
arithmetic should be verified in R (cheap) rather than in the full ring A (expensive).
M2 naturally computes with coefficients in R. The Algebra extension lifts coefficient
operations to R and uses algebraMap to connect.

Tests that grind can't yet close are marked with sorry and a comment explaining
what the extension would need to do.
-/

import Macaulean.Grind.Algebra.Extension

open Lean Grind

variable {R : Type u} {A : Type v}

/-! ## Group 1: Coefficient product verification

When M2 returns a factorization, we verify f₁ * f₂ = g. The coefficients multiply
in R. These tests check that coefficient multiplication can be verified via R
rather than in the full ring A. -/

-- M2 says: coefficient c₁ * c₂ = c₃ in R.
-- Without algebra: three opaque vars in A, Gröbner can't relate them.
-- With algebra: lift to R, use h, done.
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ c₃ : R) (h : c₁ * c₂ = c₃) :
    algebraMap R A c₁ * algebraMap R A c₂ = algebraMap R A c₃ := by
  rw [← Algebra.algebraMap_mul, h]

-- M2 says this coefficient sum is zero.
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (h : c₁ + c₂ = 0) :
    algebraMap R A c₁ + algebraMap R A c₂ = 0 := by
  rw [← Algebra.algebraMap_add, h, Algebra.algebraMap_zero]

-- M2 factors a coefficient: c = a * b in R.
-- The factored form in A should match.
example [CommRing R] [CommRing A] [Algebra R A]
    (a b c : R) (h : a * b = c) (x : A) :
    algebraMap R A a * (algebraMap R A b * x) = algebraMap R A c * x := by
  rw [← Semiring.mul_assoc, ← Algebra.algebraMap_mul, h]

/-! ## Group 2: Coefficient collection — expressions in im(algebraMap)

When the entire expression lives in im(algebraMap), normalization should happen
in R not A. This is the "small subalgebra" case. -/

-- Pure coefficient expression: verify a product in the subalgebra.
-- Gröbner in A sees 4 opaque vars. Lift to R: (r+s)*(r-s) = r²-s².
example [CommRing R] [CommRing A] [Algebra R A] (r s : R) :
    (algebraMap R A r + algebraMap R A s) *
    (algebraMap R A r - algebraMap R A s) =
    algebraMap R A (r * r - s * s) := by
  sorry -- Extension needs: detect all terms in im(algebraMap), lift entire expression to R, normalize there

-- Three-factor product: trivial lift to R.
example [CommRing R] [CommRing A] [Algebra R A] (r s t : R) :
    algebraMap R A r * algebraMap R A s * algebraMap R A t =
    algebraMap R A (r * s * t) := by
  rw [← Algebra.algebraMap_mul, ← Algebra.algebraMap_mul]

-- Coefficient square: (r+s)² in A via R
example [CommRing R] [CommRing A] [Algebra R A] (r s : R) :
    (algebraMap R A r + algebraMap R A s) *
    (algebraMap R A r + algebraMap R A s) =
    algebraMap R A (r * r + r * s + s * r + s * s) := by
  sorry -- Extension needs: detect im(algebraMap), lift, normalize in R, push back

/-! ## Group 3: Mixed coefficient + variable — the polynomial ring case

The typical M2 result: polynomials with coefficients in R and variables in A.
Coefficient ops verified in R, variable structure in A. -/

-- Distribute a coefficient across a sum of A-terms.
-- Core pattern: scalar * polynomial = sum of scaled monomials.
example [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (x y : A) :
    algebraMap R A r * (x + y) = algebraMap R A r * x + algebraMap R A r * y := by
  grind

-- Two-term polynomial multiplication:
-- (c₁*x) * (c₂*y) = (c₁*c₂)*(x*y)
-- Coefficient part verified in R, variable part is just x*y.
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x y : A) :
    (algebraMap R A c₁ * x) * (algebraMap R A c₂ * y) =
    algebraMap R A (c₁ * c₂) * (x * y) := by
  sorry -- Extension needs: factor coefficient product through R, rearrange using commutativity

-- Collect like terms: c₁*x + c₂*x = (c₁+c₂)*x
-- Coefficient addition in R, factoring in A.
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    algebraMap R A c₁ * x + algebraMap R A c₂ * x =
    algebraMap R A (c₁ + c₂) * x := by
  sorry -- Extension needs: detect common A-factor, collect coefficients in R

-- smul version of above (the way M2 results typically arrive)
example [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    c₁ • x + c₂ • x = (c₁ + c₂) • x := by
  sorry -- Extension needs: rewrite smul → algebraMap, then collect

/-! ## Group 4: M2-style verification with coefficient hypotheses

M2 computed a result and gave us coefficient relations. We verify using those
relations without expanding everything in A. -/

-- M2 says this polynomial vanishes because the coefficient relation holds.
example [CommRing R] [CommRing A] [Algebra R A]
    (a b c : R) (x : A)
    (h : a * b - c = 0) :
    algebraMap R A a * (algebraMap R A b * x) - algebraMap R A c * x = 0 := by
  sorry -- Extension needs: lift a*b to R, use h to get a*b = c, substitute

-- M2 gives a linear combination certificate:
-- a₁*f₁ + a₂*f₂ = g, verified via coefficient identity a₁ + a₂ = 1.
example [CommRing R] [CommRing A] [Algebra R A]
    (a₁ a₂ : R) (x : A)
    (h : a₁ + a₂ = 1) :
    a₁ • x + a₂ • x = x := by
  sorry -- Extension needs: rewrite smul, collect coefficients in R, use h, algebraMap 1 = 1

-- Coefficient cancellation from M2 result
example [CommRing R] [CommRing A] [Algebra R A]
    (r s : R) (x : A)
    (h : r * s = s * r) :
    algebraMap R A r * (algebraMap R A s * x) =
    algebraMap R A s * (algebraMap R A r * x) := by
  sorry -- Extension needs: use algebraMap commutes with A, or lift coefficient commutativity

/-! ## Group 5: Stress test — where subalgebra lifting really pays off -/

-- Large coefficient expression. In A: 6 opaque variables, full expansion.
-- Lift to R: it's (a+b+c)*(d+e+f), one polynomial multiplication.
example [CommRing R] [CommRing A] [Algebra R A]
    (a b c d e f : R) :
    (algebraMap R A a + algebraMap R A b + algebraMap R A c) *
    (algebraMap R A d + algebraMap R A e + algebraMap R A f) =
    algebraMap R A (a*d + a*e + a*f + b*d + b*e + b*f + c*d + c*e + c*f) := by
  sorry -- Extension needs: full subalgebra detection + lift + normalize in R

-- Given a nontrivial coefficient identity, collapse a big expression.
-- Without lifting: Gröbner in A can't use h.
-- With lifting: apply h in R, expression simplifies.
example [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (x : A)
    (h : r * r * r = r) :
    algebraMap R A r * algebraMap R A r * algebraMap R A r * x =
    algebraMap R A r * x := by
  sorry -- Extension needs: detect r³ in im(algebraMap), lift to R, apply h, push back
