import Macaulean.Verification.MathematicalExport

namespace MathematicalExportTest
open M2
open Macaulean.M2.Verification.Views

R = QQ[x,y];
p = x^2-y;
I = ideal(x^2-y,x*y-1);

#m2_export "p" as p_math
#m2_export "I" as I_math

example : readPolynomial M2Generated.R p_math.source = .ok p_math :=
  p_math.source_eq
example : readIdeal M2Generated.R I_math.source = .ok I_math :=
  I_math.source_eq
example : I_math.generators.length = 2 := rfl
example : p_math.coeff [2,0] = 1 := by decide +kernel
example : p_math.coeff [0,1] = -1 := by decide +kernel

-- Later assignment cannot change the mathematical object already exported.
I = ideal(x);
#m2_export "I" as J_math
example : I_math.generators.length = 2 := rfl
example : J_math.generators.length = 1 := rfl

/-- error: mathematical export currently expects a polynomial or ideal -/
#guard_msgs in
#m2_export "R" as unsupported

/-- error: no worksheet binding exported for absent -/
#guard_msgs in
#m2_export "absent" as missing

-- Explicit Lean presentations can be sent back through the runtime boundary.
example : readIdeal M2Generated.R I_math.value = .ok I_math :=
  ideal_roundtrip I_math

example : readIdeal M2Generated.R
    (.algebra (.ideal { M2Generated.R with id := 1000 } [])) =
    .error "ideal view: foreign ring identity" := rfl

example : readIdeal M2Generated.R
    (.algebra (.ideal M2Generated.R [[(1, [1])]])) =
    .error "polynomial exponent vector has the wrong dimension" := rfl

/-- info: 'MathematicalExportTest.I_math.source_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms I_math.source_eq

end MathematicalExportTest
