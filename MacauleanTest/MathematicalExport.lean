import Macaulean.Verification.MathematicalExport

namespace MathematicalExportTest
open M2
open Macaulean.Algebra
open Macaulean.M2.Verification.MathematicalViews

Q = QQ;
R = Q[x,y];
p = x^2-y;
q = x*y-1;
f = x^3-1;
I = ideal(p,q);

#m2_export "Q" as Q_math
#m2_export "R" as R_math
#m2_export "x" as x_math
#m2_export "p" as p_math
#m2_export "q" as q_math
#m2_export "f" as f_math
#m2_export "I" as I_math

example : readField Q_math.source = .ok Q_math := Q_math.source_eq
example : readRing R_math.source = .ok R_math := R_math.source_eq
example : readPolynomial R_math p_math.source = .ok p_math := p_math.source_eq
example : readIdeal R_math I_math.source = .ok I_math := I_math.source_eq
example : I_math.generators.length = 2 := rfl
example : p_math.coeff ⟨[2,0],rfl⟩ = 1 := by decide +kernel
example : p_math.coeff ⟨[0,1],rfl⟩ = -1 := by decide +kernel

-- A theorem about the ideal actually constructed by the worksheet.
theorem membership : I_math.Member f_math := by
  change Generated [p_math.data,q_math.data] f_math.data
  apply Generated.equivalent (p := Macaulean.M2.KernelPolynomial.add
    (Macaulean.M2.KernelPolynomial.mul x_math.data p_math.data) q_math.data)
  · apply Polynomial.equivalent_of_normalize_eq
    apply eq_of_beq
    decide +kernel
  · exact .add (.mul x_math.data (.generator (by simp))) (.generator (by simp))

-- Later assignment cannot change the mathematical object already exported.
I = ideal(x);
#m2_export "I" as J_math
example : I_math.generators.length = 2 := rfl
example : J_math.generators.length = 1 := rfl

n = 42;
/-- error: mathematical export expects a coefficient field, polynomial ring, polynomial, or ideal -/
#guard_msgs in
#m2_export "n" as unsupported

/-- error: no worksheet binding exported for absent -/
#guard_msgs in
#m2_export "absent" as missing

example : readIdeal R_math (idealValue I_math) = .ok I_math := ideal_roundtrip I_math
example : readRing (ringValue R_math) = .ok R_math := ring_roundtrip R_math
example : readIdeal R_math
    (.algebra (.ideal { M2Generated.R with id := 1000 } [])) =
    .error "ideal view: foreign ring identity" := rfl
example : readIdeal R_math
    (.algebra (.ideal M2Generated.R [[(1, [1])]])) =
    .error "polynomial exponent vector has the wrong dimension" := rfl

/-- info: 'MathematicalExportTest.I_math.source_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms I_math.source_eq
/-- info: 'MathematicalExportTest.membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms membership
end MathematicalExportTest

namespace FiniteMathematicalExportTest
open M2
open Macaulean.Algebra
open Macaulean.M2.Verification.MathematicalViews

K = GF(5);
R = K[u,v];
p = u^2-v;
q = u*v-1;
f = u^3-1;
I = ideal(p,q);

#m2_export "K" as K_math
#m2_export "R" as R_math
#m2_export "u" as u_math
#m2_export "p" as p_math
#m2_export "q" as q_math
#m2_export "f" as f_math
#m2_export "I" as I_math

example : Lean.Grind.Field K_math.Carrier := inferInstance
example : K_math.characteristic = 5 := rfl
example : readField K_math.source = .ok K_math := K_math.source_eq
example : readRing R_math.source = .ok R_math := R_math.source_eq
example : readPolynomial R_math p_math.source = .ok p_math := p_math.source_eq
example : readIdeal R_math I_math.source = .ok I_math := I_math.source_eq
example : I_math.generators.length = 2 := rfl
example : p_math.coeff ⟨[0,1],rfl⟩ = 4 := by decide +kernel
theorem membership : I_math.Member f_math := by
  change Generated [p_math.data,q_math.data] f_math.data
  apply Generated.equivalent (p := Macaulean.M2.KernelPolynomial.add
    (Macaulean.M2.KernelPolynomial.mul u_math.data p_math.data) q_math.data)
  · apply Polynomial.equivalent_of_normalize_eq
    apply eq_of_beq
    decide +kernel
  · exact .add (.mul u_math.data (.generator (by simp))) (.generator (by simp))

example : readIdeal R_math (idealValue I_math) = .ok I_math := ideal_roundtrip I_math
example : readPolynomial R_math (polynomialValue p_math) = .ok p_math := polynomial_roundtrip p_math

example : readRing (Macaulean.M2.Finite.wrap (.ring ⟨0,2,["u","v"]⟩)) =
    .error "coefficient field failed its inverse-law check" := rfl
example : readPolynomial R_math (Macaulean.M2.Finite.wrap (.poly ⟨R_math.id,3,["u","v"]⟩ [(5,[1,0])])) =
    .error "finite-field coefficient is not a canonical residue" := rfl

/-- info: 'FiniteMathematicalExportTest.I_math.source_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms I_math.source_eq
/-- info: 'FiniteMathematicalExportTest.membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms membership
end FiniteMathematicalExportTest
