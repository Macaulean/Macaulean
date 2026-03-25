import Macaulean
import Init.Data.Rat.Lemmas
import Init.Grind.Ordered.Rat

example (x y : Rat) : Macaulean.SumOfSquares.SosWitness (x^2 + y^2) := by
  m2sos_witness

example (x y : Rat) :
    let w := m2sos_witness% (x^2 + y^2)
    (w.scale : Rat) * (x^2 + y^2) = w.witness := by
  intro w
  exact w.equality

example (x y : Rat) :
    let w := m2sos_witness% ((3/2 : Rat) * x^2 + (5/3 : Rat) * y^2)
    (w.scale : Rat) * ((3/2 : Rat) * x^2 + (5/3 : Rat) * y^2) = w.witness := by
  intro w
  exact w.equality

example (x y : Rat) : 0 ≤ x^2 + y^2 := by
  m2sos

example (x y : Rat) : 0 ≤ x^4 + 2*x^2*y^2 + y^4 := by
  m2sos

example (x : Rat) : 0 ≤ (1/2 : Rat) * x^2 := by
  m2sos

example (x y : Rat) : 0 ≤ (3/2 : Rat) * x^2 + (5/3 : Rat) * y^2 := by
  m2sos

/--
error: SDP solved, dual infeasible
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

/--
error: m2sos encountered an unsupported subterm:
  x / y
-/
#guard_msgs in
example (x y : Rat) : Macaulean.SumOfSquares.SosWitness (x / y) := by
  m2sos_witness
