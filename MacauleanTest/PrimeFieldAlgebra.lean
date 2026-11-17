import Macaulean.Algebra.PrimeField
import Macaulean.Algebra.Polynomial
import Macaulean.Algebra.CoefficientField
import Macaulean.Algebra.FinitePolynomialData

namespace PrimeFieldAlgebraTest
open Macaulean Macaulean.Algebra
open Macaulean.M2.KernelPolynomial

example : PrimeField.Valid 0 := by decide +kernel
example : PrimeField.Valid 1 := by decide +kernel
example : PrimeField.Valid 3 := by decide +kernel
example : PrimeField.Valid 5 := by decide +kernel
example : ¬PrimeField.Valid 2 := by decide +kernel
example : ¬PrimeField.Valid 4 := by decide +kernel
example : ¬PrimeField.Valid 7 := by decide +kernel

#guard (match PrimeField.check 0 with | .error _ => true | .ok _ => false)
#guard (match PrimeField.check 1 with | .error _ => true | .ok _ => false)
#guard (match PrimeField.check 4 with | .error _ => true | .ok _ => false)
#guard (match PrimeField.check 5 with | .ok F => F.characteristic == 5 | .error _ => false)

-- The proof supplies Lean's actual field laws for the residue operations.
def F5 : PrimeField.Checked := ⟨3, by decide +kernel⟩
example : (2 : F5.Carrier) * (2 : F5.Carrier)⁻¹ = 1 :=
  Lean.Grind.Field.mul_inv_cancel (by decide +kernel)
example : (0 : F5.Carrier)⁻¹ = 0 := Lean.Grind.Field.inv_zero
example : (3 : F5.Carrier) + 4 = 2 := by decide +kernel

private def poly (ts : List (F5.Carrier × Nat × Nat)) : Macaulean.Polynomial F5.Carrier 2 :=
  ⟨ts.map fun (c,i,j) => ⟨c, ⟨[i,j],rfl⟩⟩⟩

def x := poly [(1,1,0)]
def g1 := poly [(1,2,0),(-1,0,1)]
def g2 := poly [(1,1,1),(-1,0,0)]
def f := poly [(1,3,0),(-1,0,0)]

example : FinitePolynomialData.decode 3 2 (FinitePolynomialData.encode f) = .ok f :=
  FinitePolynomialData.decode_encode f

example : FinitePolynomialData.decode 3 2 [(5,[1,0])] =
    .error "finite-field coefficient is not a canonical residue" := rfl
example : FinitePolynomialData.decode 3 2 [(1,[1])] =
    .error "polynomial exponent vector has the wrong dimension" := rfl

example : FinitePolynomialData.mul 3 2 (FinitePolynomialData.encode x) (FinitePolynomialData.encode g1) =
    .ok (FinitePolynomialData.encode (mul x g1)) := FinitePolynomialData.binary_encode _ _ _

example : Lean.Grind.Field (CoefficientField.prime F5).Carrier := inferInstance
example : Lean.Grind.Field CoefficientField.rationals.Carrier := inferInstance

-- The example intended for the worksheet bridge, already at the mathematical layer.
example : (Ideal.span [g1,g2]).contains f := by
  apply Generated.equivalent (p := add (mul x g1) g2)
  · apply Polynomial.equivalent_of_normalize_eq
    apply eq_of_beq
    decide +kernel
  · exact .add (.mul x (.generator (by simp))) (.generator (by simp))

-- Formal polynomial equality is stronger than equality of polynomial functions.
private def frobenius : Macaulean.Polynomial F5.Carrier 2 := poly [(1,5,0),(-1,1,0)]
example : ¬Polynomial.Equivalent frobenius Algebra.Polynomial.zero := by
  intro h
  have bad := h ⟨[5,0],rfl⟩
  have hn : Polynomial.coefficient frobenius ⟨[5,0],rfl⟩ ≠
      Polynomial.coefficient (Algebra.Polynomial.zero : Macaulean.Polynomial F5.Carrier 2) ⟨[5,0],rfl⟩ :=
    by decide +kernel
  exact hn bad

/-- info: 'Macaulean.Algebra.PrimeField.field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PrimeField.field

end PrimeFieldAlgebraTest
