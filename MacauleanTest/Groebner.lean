import Macaulean

open Lean Grind

namespace MacauleanTest.Groebner

-- gb_reduce should handle the same ideal membership goals as cas
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  gb_reduce

example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x - y) [x * x - y, y * y] := by
  gb_reduce

-- cas tactic should also work (gb_reduce strategy is a fallback)
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  cas

-- ============================================================================
-- Radical membership tests
-- ============================================================================

-- x ∈ √⟨x²⟩ because x² ∈ ⟨x²⟩
example {R : Type} [CommRing R] (x : R) :
    Macaulean.InRadical x [x * x] := by
  cas

-- x ∈ √⟨x³⟩ because x³ ∈ ⟨x³⟩
example {R : Type} [CommRing R] (x : R) :
    Macaulean.InRadical x [x * x * x] := by
  cas

end MacauleanTest.Groebner
