import MacauleanMathlib.GroebnerCommands

namespace RationalGroebnerTest
open M2
open Macaulean.M2.Verification.GroebnerViews
open Macaulean.Verification.Mathlib
R = QQ[x,y];
I = ideal(x^2-y,x*y-1);
G = gb I;
#m2_groebner "G" for "I" as certified
example : (grevlexOrder 2).IsGroebnerBasis (basisMeaning certified.idealEquality.basis)
    (idealMeaning certified.idealEquality.ideal) := certified
/-- info: 'RationalGroebnerTest.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified
end RationalGroebnerTest

namespace FiniteGroebnerTest
open M2
open Macaulean.M2.Verification.GroebnerViews
open Macaulean.Verification.Mathlib
K = GF(5);
R = K[u,v];
I = ideal(2*u^2-2*v,3*u*v-3);
G = gb I;
#m2_groebner "G" for "I" as certified
example : (grevlexOrder 2).IsGroebnerBasis (basisMeaning certified.idealEquality.basis)
    (idealMeaning certified.idealEquality.ideal) := certified
/-- info: 'FiniteGroebnerTest.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified
Other = QQ[w];
J = ideal(w);
/-- error: ideal view: incompatible coefficient field or value -/
#guard_msgs in
#m2_groebner "G" for "J" as foreignRejected
end FiniteGroebnerTest

namespace GroebnerEdgeTest
open M2
K = GF(3);
R = K[a];
Z = ideal(0*a);
ZG = gb Z;
#m2_groebner "ZG" for "Z" as zeroCertified
U = ideal(a,1-a);
UG = gb U;
#m2_groebner "UG" for "U" as unitCertified
K2 = GF(2);
R2 = K2[b,c];
I2 = ideal(b^2-c,b*c-1);
G2 = gb I2;
#m2_groebner "G2" for "I2" as characteristicTwoCertified
end GroebnerEdgeTest

namespace GroebnerNegativeTest
open Macaulean.Algebra.GroebnerCertificates Macaulean.Algebra.Certificates
open Macaulean.M2.KernelPolynomial
private def p (ts : List (Rat × Nat × Nat)) : Macaulean.Polynomial Rat 2 :=
  ⟨ts.map fun (c,i,j) => ⟨c,⟨[i,j],rfl⟩⟩⟩
private def x := p [(1,1,0)]
private def y := p [(1,0,1)]
private def g1 := p [(1,2,0),(-1,0,1)]
private def g2 := p [(1,1,1),(-1,0,0)]
private def z := p []
private def one := p [(1,0,0)]
-- Correct ideal membership is insufficient: this row's summands have degree 3,
-- while the S-polynomial has degree 2. The candidate is not a Gröbner basis.
example : represents (sPolynomial g1 g2) [g1,g2] [y,x.neg] = true := by decide +kernel
example : boundedRow (sPolynomial g1 g2) [g1,g2] [y,x.neg] = false := by decide +kernel
example : pair [g1,g2] g1 g2 [y,x.neg] = false := by decide +kernel
example : sameIdeal [g1,g2] [g1,g2] [[one,z],[z,one]] [[one,z],[z,one]] = true := by decide +kernel
-- Matrix dimensions cannot be omitted, even when an S-polynomial is zero.
example : checkBasis [one] [] = false := by decide +kernel
example : checkBasis [one] [[]] = false := by decide +kernel
example : checkBasis [one] [[[z,z]]] = false := by decide +kernel
example : checkBasis [z] [[[z]]] = false := by decide +kernel
example : checkBasis [one] [[[one]]] = false := by decide +kernel
example : checkBasis [one] [[[z]]] = true := by decide +kernel
end GroebnerNegativeTest
