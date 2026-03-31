import Macaulean

open Lean Grind

namespace MacauleanTest.Polyrith

/-! ### Simple cases over Int -/

example (x y : Int) (h1 : 3 * x + 2 * y = 10) :
    3 * x + 2 * y = 10 := by m2polyrith

example (x y : Int) (h1 : x * y + 2 * x = 1) (h2 : x = y) :
    x * y = -2 * y + 1 := by m2polyrith

example (x y : Int) (h1 : x + 2 = -3) (h2 : y = 10) :
    -y + 2 * x + 4 = -16 := by m2polyrith

/-! ### Systems with 3+ equations -/

example (x y z : Int) (ha : x + 2 * y - z = 4) (hb : 2 * x + y + z = -2)
    (hc : x + 2 * y + z = 2) :
    -3 * x - 3 * y - 4 * z = 2 := by m2polyrith

example (a b c d : Int) (h1 : a = 4) (h2 : 3 = b) (h3 : c * 3 = d) (h4 : -d = a) :
    2 * a - 3 + 9 * c + 3 * d = 8 - b + 3 * d - 3 * a := by m2polyrith

/-! ### Cases over Rat -/

example (x y : Rat) (h1 : x * y + 2 * x = 1) (h2 : x = y) :
    x * y = -2 * y + 1 := by m2polyrith

example (a b c d : Rat) (h1 : a = 4) (h2 : 3 = b) (h3 : c * 3 = d) (h4 : -d = a) :
    2 * a - 3 + 9 * c + 3 * d = 8 - b + 3 * d - 3 * a := by m2polyrith

example (a b c d : Rat) (h1 : a = 4) (h2 : 3 = b) (h3 : c * 3 = d) (h4 : -d = a) :
    6 - 3 * c + 3 * a + 3 * d = 2 * b - d + 12 - 3 * a := by m2polyrith

/-! ### Arbitrary polynomial coefficients -/

-- Coefficient is a (the hypothesis variable itself)
example (a b : Int) (h : a = b) : a * a = a * b := by m2polyrith

-- Coefficient is c
example (a b c : Int) (h : a = b) : a * c = b * c := by m2polyrith

-- Two hypotheses with polynomial witness
example (a b c : Int) (h1 : a = b) (h2 : b = 1) : c * a + b = c * b + 1 := by m2polyrith

-- Nontrivial polynomial combination: x*y*h1 + 2*h2
example (x y : Int) (h1 : x + y = 3) (h2 : 3 * x = 7) :
    x * x * y + y * x * y + 6 * x = 3 * x * y + 14 := by m2polyrith

-- Cross-term: (x + 2*y) * hzw
example (x y z w : Int) (hzw : z = w) :
    x * z + 2 * y * z = x * w + 2 * y * w := by m2polyrith

/-! ### Abstract CommRing -/

example {R : Type} [CommRing R] {a b c d e f : R}
    (h1 : a * d = b * c) (h2 : c * f = e * d) :
    c * (a * f - b * e) = 0 := by m2polyrith

/-! ### Degenerate cases -/

-- Solving for a variable (integer coefficient suffices)
example (x : Int) (h1 : x + 4 = 2) : x = -2 := by m2polyrith

example (x : Int) (h1 : 2 * x + 3 = x) : x = -3 := by m2polyrith

example (c : Rat) (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by m2polyrith

/-! ### Powers -/

example (x y : Int) (h : x = 0) : y ^ 2 * x = 0 := by m2polyrith

/-! ### `only` syntax -/

example (x y : Int) (h1 : x = y) (h2 : y = 0) : x = 0 := by
  m2polyrith only [h1, h2]

-- Select specific hypotheses, ignoring irrelevant ones
example (a b c : Int) (h1 : a = b) (h2 : b = c) (h_noise : a + b + c = 42) :
    a = c := by
  m2polyrith only [h1, h2]

/-! ### Known limitations
  The following patterns do NOT work with the current ZZ backend:

  1. Goals requiring rational coefficients (e.g., `3*w + 1 = 4 ⊢ w = 1` needs q = 1/3)
  2. Nullstellensatz cases requiring exponent > 1 (e.g., `x = y, x*y = 0 ⊢ x + y*z = 0`)
  3. Goals over fields with division (e.g., `b = 2/3`)
  4. Inequalities (we only handle equalities)
  5. Scalar multiplication / module cases
-/

end MacauleanTest.Polyrith
