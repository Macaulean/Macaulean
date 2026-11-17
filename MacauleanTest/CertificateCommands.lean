import Macaulean.Verification.CertificateCommands

namespace RationalCertificateTest
open M2
open Macaulean.Algebra
R = QQ[x,y];
I = ideal(x^2-y,x*y-1);
f = x^3-1;
G = gb I;
#m2_export "I" as I_math
#m2_export "f" as f_math
#m2_membership "f" in "I" as f_in_I
example : I_math.Member f_math := f_in_I
#m2_ideal_equality "G" for "I" as same_ideal
example : Ideal.Same I_math.meaning same_ideal.basis.output.meaning := same_ideal

/-- info: 'RationalCertificateTest.f_in_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms f_in_I
/-- info: 'RationalCertificateTest.same_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms same_ideal

bad = x;
/-- error: the computed coefficient row does not prove ideal membership -/
#guard_msgs in
#m2_membership "bad" in "I" as rejected
end RationalCertificateTest

namespace FiniteCertificateTest
open M2
open Macaulean.Algebra
K = GF(5);
R = K[u,v];
I = ideal(u^2-v,u*v-1);
f = u^3-1;
G = gb I;
#m2_export "I" as I_math
#m2_export "f" as f_math
#m2_membership "f" in "I" as f_in_I
example : I_math.Member f_math := f_in_I
#m2_ideal_equality "G" for "I" as same_ideal
example : Ideal.Same I_math.meaning same_ideal.basis.output.meaning := same_ideal

/-- info: 'FiniteCertificateTest.f_in_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms f_in_I
/-- info: 'FiniteCertificateTest.same_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms same_ideal

bad = u;
/-- error: the computed coefficient row does not prove ideal membership -/
#guard_msgs in
#m2_membership "bad" in "I" as rejected
end FiniteCertificateTest

namespace CertificateNegativeTests
open Macaulean.Algebra
open Macaulean.Algebra.Certificates
open Macaulean.M2.Verification.CertificateData

-- A row accepted in one direction is insufficient for equality of ideals.
private def poly (c : Rat) (i j : Nat) : Macaulean.Polynomial Rat 2 :=
  ⟨[⟨c,⟨[i,j],rfl⟩⟩]⟩
private def x := poly 1 1 0
private def y := poly 1 0 1
private def one := poly 1 0 0
private def zero : Macaulean.Polynomial Rat 2 := ⟨[]⟩
example : rows [x] [x,y] [[one,zero]] = true := by decide +kernel
example : sameIdeal [x,y] [x] [[one,zero]] [[one],[zero]] = false := by decide +kernel
example : represents zero [x] [] = false := by decide +kernel
example : represents x [x] [one,zero] = false := by decide +kernel
example : rows [] [x] [[]] = false := by decide +kernel
example : sameIdeal ([] : List (Macaulean.Polynomial Rat 2)) [] [] [] = true := by decide +kernel
example : checkIdealEquality RationalCertificateTest.I_math RationalCertificateTest.same_ideal.basis [] = false :=
  by decide +kernel
example : checkIdealEquality FiniteCertificateTest.I_math
    { FiniteCertificateTest.same_ideal.basis with representations := [] }
    FiniteCertificateTest.same_ideal.reverseRows = false := by decide +kernel
end CertificateNegativeTests

namespace DegenerateCertificateTests
open M2
K = GF(3);
R = K[a,b];
I = ideal(0*a);
f = 0*a;
G = gb I;
#m2_membership "f" in "I" as zero_member
#m2_ideal_equality "G" for "I" as zero_ideal
J = ideal(a,1-a);
h = a^5+b^3;
H = gb J;
#m2_membership "h" in "J" as unit_member
#m2_ideal_equality "H" for "J" as unit_ideal

S = QQ[z];
foreign = z;
/-- error: polynomial view: incompatible coefficient field or value -/
#guard_msgs in
#m2_membership "foreign" in "I" as rejected
end DegenerateCertificateTests
