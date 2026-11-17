import Macaulean.Interpreter.DSL

namespace FiniteFieldWorksheet
open M2

/-- info: o1 = GF(5) : Type -/
#guard_msgs in
K = GF(5)
/-- info: o2 = GF(5)[x, y] : PolynomialRing -/
#guard_msgs in
R = K[x,y]
I = ideal(x^2-y,x*y-1);
G = gb I;
/-- info: o5 = matrix{{y^2 + 4*x, x*y + 4, x^2 + 4*y}} : Matrix -/
#guard_msgs in
gens G
/-- info: o6 = 0 : GF(5)[x, y] -/
#guard_msgs in
(x^3-1) % G
/-- info: o7 = true : Boolean -/
#guard_msgs in
(gens I)*(getChangeMatrix G) == gens G
/-- info: o8 = 2*x : GF(5)[x, y] -/
#guard_msgs in
3*x+4*x
/-- info: o9 = 3 : GF(5) -/
#guard_msgs in
1/(leadCoefficient (2*x))
/-- info: o10 = 0 : GF(5)[x, y] -/
#guard_msgs in
(x+y)^5-x^5-y^5
/-- info: o11 = false : Boolean -/
#guard_msgs in
x^5-x == 0

-- Nontrivial coefficients exercise modular division inside the source algorithm.
J = ideal(2*x^2+3*y,4*x*y+1);
H = gb J;
/-- info: o14 = true : Boolean -/
#guard_msgs in
(gens J)*(getChangeMatrix H) == gens H
/-- info: o15 = 0 : GF(5)[x, y] -/
#guard_msgs in
(2*x^2+3*y) % H

-- Reusing indeterminate names still creates a distinct ring identity.
oldx = x;
K7 = GF(7);
S = K7[x,y];
/-- error: polynomials belong to different rings -/
#guard_msgs in
oldx + x

/-- error: the characteristic does not define a prime field -/
#guard_msgs in
GF(4)
/-- error: a prime field characteristic must be at least two -/
#guard_msgs in
GF(1)
/-- error: division by zero -/
#guard_msgs in
1/(promote(0,GF(7)))

-- Rational promotion is partial: denominators must remain nonzero.
/-- info: o23 = 4*x : GF(7)[x, y] -/
#guard_msgs in
(1/2)*x
/-- error: division by zero -/
#guard_msgs in
(1/7)*x
/-- error: no method for operator == applied to objects of class Ideal, Ideal -/
#guard_msgs in
I == I

end FiniteFieldWorksheet
