import MacauleanMathlib.GroebnerCommands
import Macaulean.Verification.MathematicalImport

namespace MathematicalImportTest
open Macaulean.Algebra
open M2

-- A finite Lean presentation becomes an ordinary worksheet ring and ideal.
def leanRing : PolynomialRing := ⟨.rationals,1000,["lx","ly"]⟩
def leanPoly (ts : List (Rat × Nat × Nat)) : RingPolynomial leanRing :=
  ⟨⟨ts.map fun (c,i,j) => ⟨c,⟨[i,j],rfl⟩⟩⟩⟩
def leanIdeal : IdealPresentation leanRing :=
  ⟨[leanPoly [(1,2,0),(-1,0,1)], leanPoly [(1,1,1),(-1,0,0)]]⟩
def leanMember := leanPoly [(1,3,0),(-1,0,0)]
#m2_import leanRing as "LR"
#m2_import leanIdeal as "LI"
#m2_import leanMember as "lf"
LG = gb LI;
#m2_groebner "LG" for "LI" as certified
#m2_membership "lf" in "LI" as membership
#m2_export "LR" as returnedRing
#m2_export "LI" as returnedIdeal
#m2_export "lf" as returnedMember
example : returnedRing = leanRing := rfl
example : returnedIdeal = leanIdeal := rfl
example : returnedMember = leanMember := rfl
example : leanIdeal.Member leanMember := membership
-- Importing a ring publishes its variables and reserves its identity.
samePolynomial = lf == lx^3-1;
example : M2Generated.samePolynomial = true := rfl

-- The finite-field direction uses the same import and certification commands.
def leanField : CoefficientField := .prime ⟨3,by decide +kernel⟩
def finiteRing : PolynomialRing := ⟨leanField,1001,["fx","fy"]⟩
def finitePoly (ts : List (leanField.Carrier × Nat × Nat)) : RingPolynomial finiteRing :=
  ⟨⟨ts.map fun (c,i,j) => ⟨c,⟨[i,j],rfl⟩⟩⟩⟩
def finiteIdeal : IdealPresentation finiteRing :=
  ⟨[finitePoly [(1,2,0),(-1,0,1)], finitePoly [(1,1,1),(-1,0,0)]]⟩
#m2_import leanField as "FK"
#m2_import finiteRing as "FR"
#m2_import finiteIdeal as "FI"
FG = gb FI;
#m2_groebner "FG" for "FI" as finiteCertified
#m2_export "FI" as finiteReturned
example : finiteReturned = finiteIdeal := rfl

-- Reusing an allocated identity for a different ring must fail atomically.
def conflicting : PolynomialRing := ⟨.rationals,1000,["other"]⟩
/-- error: imported ring identity conflicts with the worksheet; use a fresh identity or an exported ring -/
#guard_msgs in
#m2_import conflicting as "badRing"

/-- error: imported ring has duplicate variable names -/
#guard_msgs in
#m2_import (⟨.rationals,2000,["dup","dup"]⟩ : PolynomialRing) as "duplicateRing"

/-- error: import expects a coefficient field, polynomial ring, polynomial, or finite ideal presentation -/
#guard_msgs in
#m2_import (5 : Nat) as "integer"

-- An import respects protected names and preserves the existing worksheet.
/-- error: attempted to modify a protected symbol 'QQ' -/
#guard_msgs in
#m2_import leanMember as "QQ"
#m2_export "LI" as afterRejectedImports
example : afterRejectedImports = leanIdeal := rfl

/-- error: import binding must be an M2 identifier -/
#guard_msgs in
#m2_import leanMember as "bad_name"

-- A new worksheet-created ring receives a fresh identity after the imported one.
Next = QQ[next];
#m2_export "Next" as nextRing
example : nextRing.id > finiteRing.id := by decide +kernel
end MathematicalImportTest
