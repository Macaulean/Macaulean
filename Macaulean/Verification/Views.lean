import Macaulean.Interpreter.Polynomials

/-!
# Checked mathematical views

The ring is a type index, not a printed name. Decoding preserves coefficient and
exponent data and rejects foreign rings and malformed dimensions. Equality in the
mathematical view is coefficientwise, not equality of a particular sparse list.
No correctness theorem for polynomial normalization is assumed here.
-/
namespace Macaulean.M2.Verification.Views
open Polynomials

structure Polynomial (ring : RingInfo) where
  data : Macaulean.Polynomial Rat ring.names.length

structure Row (ring : RingInfo) (length : Nat) where
  values : List (Polynomial ring)
  size_eq : values.length = length

def Polynomial.raw (p : Polynomial r) : Raw := encode p.data

def Polynomial.value (p : Polynomial r) : Value := .algebra (.poly r p.raw)

def readPolynomial (r : RingInfo) : Value → Except String (Polynomial r)
  | .algebra (.poly s raw) =>
    if r = s then Polynomial.mk <$> decode r.names.length raw
    else .error "polynomial view: foreign ring identity"
  | _ => .error "polynomial view: expected a polynomial"

def readPolynomials (r : RingInfo) : List Value → Except String (List (Polynomial r))
  | [] => .ok []
  | v :: vs => do return (← readPolynomial r v) :: (← readPolynomials r vs)

def readRow (r : RingInfo) (n : Nat) (v : Value) : Except String (Row r n) := do
  let xs ← match v with
    | .list xs | .sequence xs => readPolynomials r xs
    | .algebra (.row s ps) =>
      if r = s then readPolynomials r (ps.map fun p => .algebra (.poly s p))
      else .error "coefficient-row view: foreign ring identity"
    | _ => .error "coefficient-row view: expected a list, sequence or generator row"
  if h : xs.length = n then return ⟨xs,h⟩
  else .error "coefficient-row view: wrong length"

/-- A coefficient query sums duplicates, so order and sparse-list layout are not
part of the mathematical meaning. -/
def coefficient (raw : Raw) (powers : List Nat) : Rat :=
  raw.foldr (fun (c,ns) total => (if ns = powers then c else 0) + total) 0

def Polynomial.coeff (p : Polynomial r) (powers : List Nat) : Rat :=
  coefficient p.raw powers

def Equivalent (p q : Polynomial r) : Prop := ∀ powers, p.coeff powers = q.coeff powers

/-- Coefficient of a product, defined by finite convolution independently of the
production multiplication implementation. -/
def productCoefficient (p q : Polynomial r) (powers : List Nat) : Rat :=
  p.raw.foldr (fun (a,as) total => total +
    q.raw.foldr (fun (b,bs) subtotal =>
      (if (as.zip bs).map (fun (i,j) => i+j) = powers then a*b else 0) + subtotal) 0) 0

def linearCoefficient : List (Polynomial r) → List (Polynomial r) → List Nat → Rat
  | [], _, _ => 0
  | _, [], _ => 0
  | a :: as, b :: bs, powers => productCoefficient a b powers + linearCoefficient as bs powers

/-- The dimension-indexed row prevents the truncation in `linearCoefficient`
from weakening the intended representation relation. -/
def Represents (p : Polynomial r) (generators : List (Polynomial r))
    (coefficients : Row r generators.length) : Prop :=
  ∀ powers, p.coeff powers = linearCoefficient coefficients.values generators powers

def DifferenceInIdeal (f remainder : Polynomial r) (generators : List (Polynomial r)) : Prop :=
  ∃ coefficients : Row r generators.length, ∀ powers,
    f.coeff powers - remainder.coeff powers =
      linearCoefficient coefficients.values generators powers

/-- The fixed grevlex view is inherited from the polynomial layer. Its semantic
dependency is pinned with any approval that mentions remainder irreducibility. -/
def Polynomial.leadingPowers? (p : Polynomial r) : Option (List Nat) :=
  (KernelPolynomial.normalize p.data).terms.head? |>.map (fun t => t.monomial.powers)

def Irreducible (p : Polynomial r) (generators : List (Polynomial r)) : Prop :=
  ∀ powers, p.coeff powers ≠ 0 → ∀ g ∈ generators, ∀ leading,
    g.leadingPowers? = some leading → divides leading powers = false

def OrderedRemainder (f remainder : Polynomial r) (generators : List (Polynomial r)) : Prop :=
  DifferenceInIdeal f remainder generators ∧ Irreducible remainder generators

theorem polynomial_roundtrip (p : Polynomial r) :
    readPolynomial r p.value = .ok p := by
  cases p
  simp [readPolynomial, Polynomial.value, Polynomial.raw, decode_encode,
    Functor.map, Except.map]

theorem polynomial_foreign_ring (r s : RingInfo) (raw : Raw) (h : r ≠ s) :
    readPolynomial r (.algebra (.poly s raw)) = .error "polynomial view: foreign ring identity" := by
  simp [readPolynomial,h]

theorem polynomial_exponent_dimension (p : Polynomial r) (t : Rat × List Nat)
    (h : t ∈ p.raw) : t.2.length = r.names.length := encode_dimension p.data t h

theorem row_dimension (row : Row r n) : row.values.length = n := row.size_eq

theorem equivalent_refl (p : Polynomial r) : Equivalent p p := fun _ => rfl

theorem equivalent_symm (p q : Polynomial r) (h : Equivalent p q) : Equivalent q p :=
  fun powers => (h powers).symm

theorem equivalent_trans (p q t : Polynomial r) (h : Equivalent p q) (k : Equivalent q t) :
    Equivalent p t := fun powers => (h powers).trans (k powers)

theorem coefficient_nil (powers : List Nat) : coefficient [] powers = 0 := rfl

theorem coefficient_cons (c : Rat) (ns powers : List Nat) (tail : Raw) :
    coefficient ((c,ns)::tail) powers =
      (if ns = powers then c else 0) + coefficient tail powers := rfl

theorem represents_dimension (p : Polynomial r) (gs : List (Polynomial r))
    (row : Row r gs.length) (_ : Represents p gs row) : row.values.length = gs.length :=
  row.size_eq

end Macaulean.M2.Verification.Views
