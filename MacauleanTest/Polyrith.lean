import Macaulean

open Lean Grind

namespace MacauleanTest.Polyrith

-- Single hypothesis substitution
example (x y : Int) (h : x = y) : x = y := by
  m2polyrith

-- Linear combination of two hypotheses
example (x y z : Int) (h1 : x = y + 1) (h2 : y = z) : x = z + 1 := by
  m2polyrith

-- Polynomial hypothesis
example (x y : Int) (h : x * x = y) : x * x * x = x * y := by
  m2polyrith

-- Multiple hypotheses needed
example (a b c : Int) (h1 : a = b + c) (h2 : b = c) : a = 2 * c := by
  m2polyrith

-- Using `only` syntax
example (x y : Int) (h1 : x = y) (h2 : y = 0) : x = 0 := by
  m2polyrith only [h1, h2]

-- Concrete arithmetic
example (x y : Int) (h : x = y + 3) : x - 3 = y := by
  m2polyrith

end MacauleanTest.Polyrith
