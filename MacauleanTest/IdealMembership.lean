import Macaulean

open Lean Grind

namespace MacauleanTest.IdealMembership

-- Test cas tactic on ideal membership goals
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  cas

example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x - y) [x * x - y, y * y] := by
  cas

/--
error: Tactic `cas` failed: CAS did not certify that the element is in the ideal

R : Type
inst✝ : CommRing R
x y : R
⊢ Macaulean.InIdeal (x * x * x) [x * x - y, y * y]
-/
#guard_msgs in
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x) [x * x - y, y * y] := by
  cas

-- Legacy wrapper still works
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  m2ideal_member

end MacauleanTest.IdealMembership
