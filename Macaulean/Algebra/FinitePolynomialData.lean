import Macaulean.Algebra.PrimeField
import Macaulean.Interpreter.KernelPolynomial

/-! Checked encoding of sparse polynomials over modular coefficient rings.
Canonical residues and exponent dimensions are validated at the boundary.
Field certification is separate: all arithmetic here is valid for modular
commutative rings; division requires the checked prime-field contract.
-/
namespace Macaulean.Algebra.FinitePolynomialData
open Macaulean.M2.KernelPolynomial

abbrev Raw := List (Nat × List Nat)
abbrev Poly (offset variables : Nat) := Macaulean.Polynomial (PrimeField.Element offset) variables

def decodeTerms (offset variables : Nat) : Raw → Except String (List (PolyTerm (PrimeField.Element offset) variables))
  | [] => .ok []
  | (c,ns)::ts => do
    if hc : c < offset+2 then
      if hn : ns.length = variables then
        return ⟨⟨c,hc⟩,⟨ns,hn⟩⟩ :: (← decodeTerms offset variables ts)
      else .error "polynomial exponent vector has the wrong dimension"
    else .error "finite-field coefficient is not a canonical residue"

def decode (offset variables : Nat) (raw : Raw) : Except String (Poly offset variables) :=
  (fun ts => ⟨ts⟩) <$> decodeTerms offset variables raw

def encode (p : Poly offset variables) : Raw :=
  p.terms.map fun t => (t.coefficient.val,t.monomial.powers)

theorem decodeTerms_encode (ts : List (PolyTerm (PrimeField.Element offset) variables)) :
    decodeTerms offset variables (ts.map fun t => (t.coefficient.val,t.monomial.powers)) = .ok ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨⟨c,hc⟩,⟨ns,hn⟩⟩
    simp [decodeTerms, hc, hn, ih, bind, Except.bind, pure, Except.pure]

theorem decode_encode (p : Poly offset variables) : decode offset variables (encode p) = .ok p := by
  cases p
  simp [decode,encode,decodeTerms_encode,Functor.map,Except.map]

def normalized (offset variables : Nat) (raw : Raw) : Except String Raw := do
  return encode (normalize (← decode offset variables raw))

def binary (offset variables : Nat) (op : Poly offset variables → Poly offset variables → Poly offset variables)
    (p q : Raw) : Except String Raw := do
  return encode (op (← decode offset variables p) (← decode offset variables q))

def add (offset variables : Nat) := binary offset variables Macaulean.M2.KernelPolynomial.add
def sub (offset variables : Nat) := binary offset variables Macaulean.M2.KernelPolynomial.sub
def mul (offset variables : Nat) := binary offset variables Macaulean.M2.KernelPolynomial.mul

theorem binary_encode (op : Poly offset variables → Poly offset variables → Poly offset variables)
    (p q : Poly offset variables) :
    binary offset variables op (encode p) (encode q) = .ok (encode (op p q)) := by
  simp [binary,decode_encode,bind,Except.bind,pure,Except.pure]

end Macaulean.Algebra.FinitePolynomialData
