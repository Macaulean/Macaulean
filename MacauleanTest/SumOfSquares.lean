import Macaulean
import Init.Data.Rat.Lemmas
import Init.Grind.Ordered.Rat

example {A : Type} [Lean.Grind.Field A] [LE A] [LT A] [Std.LawfulOrderLT A] [Std.IsLinearOrder A]
    [Lean.Grind.OrderedRing A] [Lean.Grind.Algebra Rat A] (x y : A) : 0 ≤ x^2 + y^2 := by
  m2sos

example {A : Type} [Lean.Grind.Field A] [LE A] [LT A] [Std.LawfulOrderLT A] [Std.IsLinearOrder A]
    [Lean.Grind.OrderedRing A] [Lean.Grind.Algebra Rat A] (x y : A) :
    0 ≤ (3/2 : Rat) • x^2 + (5/3 : Rat) • y^2 := by
  m2sos

example (x y : Rat) : 0 ≤ x^2 + y^2 := by
  m2sos

example (x y : Rat) : 0 ≤ x^4 + 2*x^2*y^2 + y^4 := by
  m2sos

example (x : Rat) : 0 ≤ (1/2 : Rat) * x^2 := by
  m2sos

example (x y : Rat) : 0 ≤ (3/2 : Rat) * x^2 + (5/3 : Rat) * y^2 := by
  m2sos

/--
error: m2sos failed: SDP solved, dual infeasible
-/
#guard_msgs in
example (x y : Rat) : 0 ≤ x^2 - y^2 := by
  m2sos

/--
error: m2sos encountered an unsupported subterm:
  x / y
-/
#guard_msgs in
example (x y : Rat) : 0 ≤ x / y := by
  m2sos
