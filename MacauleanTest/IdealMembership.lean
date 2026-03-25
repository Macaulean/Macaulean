import Macaulean

open Lean Grind

namespace MacauleanTest.IdealMembership

example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  m2ideal_member

example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x - y) [x * x - y, y * y] := by
  m2ideal_member

/--
error: Tactic `m2ideal_member` failed: Macaulay2 did not certify that the element is in the ideal

R : Type
inst✝ : CommRing R
x y : R
⊢ Macaulean.InIdeal (x * x * x) [x * x - y, y * y]
-/
#guard_msgs in
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x) [x * x - y, y * y] := by
  m2ideal_member

end MacauleanTest.IdealMembership
