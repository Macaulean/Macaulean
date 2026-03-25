/-
Verification tests for algebra_norm tactic.
Every theorem here must be sorry-free (#print axioms shows no sorryAx).
-/

import Macaulean.Grind.AlgPoly.Tactic
open Lean Grind
set_option linter.unusedVariables false

-- Reflective core: no coefficient hypotheses required.
theorem reflect_diff_of_squares {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (r s : R) :
    (algebraMap R A r + algebraMap R A s) *
    (algebraMap R A r - algebraMap R A s) =
    algebraMap R A (r * r - s * s) := by
  algebra_norm_reflect

theorem reflect_mixed_coeff_var {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x y : A) :
    (algebraMap R A c₁ * x) * (algebraMap R A c₂ * y) =
    algebraMap R A (c₁ * c₂) * (x * y) := by
  algebra_norm_reflect

theorem reflect_smul_collect {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    c₁ • x + c₂ • x = (c₁ + c₂) • x := by
  algebra_norm_reflect

theorem reflect_coeff_hypothesis {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (x : A) (h : r * r * r = r) :
    algebraMap R A r * algebraMap R A r * algebraMap R A r * x =
    algebraMap R A r * x := by
  algebra_norm_reflect

theorem reflect_linear_comb {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (a₁ a₂ : R) (x : A) (h : a₁ + a₂ = 1) :
    a₁ • x + a₂ • x = x := by
  algebra_norm_reflect

-- Diff of squares
theorem diff_of_squares {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (r s : R) :
    (algebraMap R A r + algebraMap R A s) *
    (algebraMap R A r - algebraMap R A s) =
    algebraMap R A (r * r - s * s) := by algebra_norm

-- Coefficient hypothesis
theorem coeff_hypothesis {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) (x : A) (h : r * r * r = r) :
    algebraMap R A r * algebraMap R A r * algebraMap R A r * x =
    algebraMap R A r * x := by algebra_norm

-- Collect like terms
theorem collect_like {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    algebraMap R A c₁ * x + algebraMap R A c₂ * x =
    algebraMap R A (c₁ + c₂) * x := by algebra_norm

-- Mixed coefficient + variable
theorem mixed_coeff_var {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x y : A) :
    (algebraMap R A c₁ * x) * (algebraMap R A c₂ * y) =
    algebraMap R A (c₁ * c₂) * (x * y) := by algebra_norm

-- 6-variable stress test
theorem six_var {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (a b c d e f : R) :
    (algebraMap R A a + algebraMap R A b + algebraMap R A c) *
    (algebraMap R A d + algebraMap R A e + algebraMap R A f) =
    algebraMap R A (a*d + a*e + a*f + b*d + b*e + b*f + c*d + c*e + c*f) := by algebra_norm

-- Coefficient product
theorem coeff_product {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ c₃ : R) (h : c₁ * c₂ = c₃) :
    algebraMap R A c₁ * algebraMap R A c₂ = algebraMap R A c₃ := by algebra_norm

-- Coefficient sum zero
theorem coeff_sum_zero {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (h : c₁ + c₂ = 0) :
    algebraMap R A c₁ + algebraMap R A c₂ = 0 := by algebra_norm

-- M2 vanishing certificate
theorem m2_vanishing {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (a b c : R) (x : A) (h : a * b - c = 0) :
    algebraMap R A a * (algebraMap R A b * x) - algebraMap R A c * x = 0 := by algebra_norm

-- smul rewriting
theorem smul_collect {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c₁ c₂ : R) (x : A) :
    c₁ • x + c₂ • x = (c₁ + c₂) • x := by algebra_norm

-- Linear combination certificate
theorem linear_comb {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (a₁ a₂ : R) (x : A) (h : a₁ + a₂ = 1) :
    a₁ • x + a₂ • x = x := by algebra_norm

theorem fallback_commute {A : Type} [CommRing A] (x y : A) :
    x + y = y + x := by
  algebra_norm

theorem reflect_ambient_hypothesis {R : Type} {A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (a₁ a₂ : R) (x y : A) (h : y = x) :
    a₁ • x + a₂ • y = (a₁ + a₂) • x := by
  algebra_norm_reflect

/--
error: algebra_norm_reflect could not solve the goal
direct attempt: no algebraMap occurrence found
after smul preprocessing: `simp` made no progress
-/
#guard_msgs in
example {A : Type} [CommRing A] (x y : A) :
    x + y = y + x := by
  algebra_norm_reflect

#print axioms diff_of_squares
#print axioms coeff_hypothesis
#print axioms six_var
#print axioms m2_vanishing
#print axioms linear_comb
