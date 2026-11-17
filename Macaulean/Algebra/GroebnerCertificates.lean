import Macaulean.Algebra.Certificates

/-!
# Executable data checks for Gröbner certificates

This module only computes. Soundness for the declared grevlex order is proved in
`MacauleanMathlib.GroebnerChecker`. Each polynomial's leading term is validated
explicitly; correctness does not rely on an unproved sorting invariant.
-/
namespace Macaulean.Algebra.GroebnerCertificates
open Lean.Grind Macaulean.M2.KernelPolynomial

variable {R : Type} [CommRing R] [DecidableEq R] {n : Nat}

abbrev Poly (R : Type) (n : Nat) := Macaulean.Polynomial R n

def leadingTerms : List (PolyTerm R n) → Bool
  | [] => true
  | t :: ts => decide (t.coefficient ≠ 0) &&
      ts.all (fun u => u.monomial.grevlex t.monomial == .lt)

def leading (p : Poly R n) : Bool := leadingTerms (normalize p).terms

def monic (p : Poly R n) : Bool :=
  leading p && match (normalize p).terms with
    | [] => false
    | t :: _ => t.coefficient == 1

/-- Exponents of the factor lcm(a,b)/a. -/
def factor (a b : Mon n) : Mon n :=
  ⟨a.powers.zipWith (fun i j => max i j - i) b.powers,
    by simp [a.powers_length, b.powers_length]⟩

def sPolynomial (p q : Poly R n) : Poly R n :=
  match (normalize p).terms, (normalize q).terms with
  | t :: _, u :: _ =>
      sub (mul ⟨[⟨u.coefficient, factor t.monomial u.monomial⟩]⟩ p)
        (mul ⟨[⟨t.coefficient, factor u.monomial t.monomial⟩]⟩ q)
  | _, _ => Polynomial.zero

/-- Degree(row coefficient) + degree(basis element) ≤ degree(target), with
negative infinity for zero polynomials. Leading-term checks are separate. -/
def degreeBound (target a b : Poly R n) : Bool :=
  match (normalize a).terms, (normalize b).terms, (normalize target).terms with
  | [], _, _ | _, [], _ => true
  | _::_, _::_, [] => false
  | t::_, u::_, v::_ => (t.monomial.mul u.monomial).grevlex v.monomial != .gt

def boundedRow (target : Poly R n) (basis row : List (Poly R n)) : Bool :=
  row.length == basis.length && leading target && row.all leading &&
    (row.zip basis).all (fun (a,b) => degreeBound target a b)

def pair (basis : List (Poly R n)) (p q : Poly R n) (row : List (Poly R n)) : Bool :=
  let s := sPolynomial p q
  Certificates.represents s basis row && boundedRow s basis row

/-- A square matrix of coefficient rows, one for every ordered pair of generators. -/
def pairRows (rows : List (List (List (Poly R n)))) (i j : Nat) : List (Poly R n) :=
  ((rows[i]?).getD [])[j]?.getD []

def checkBasis (basis : List (Poly R n)) (rows : List (List (List (Poly R n)))) : Bool :=
  basis.all monic &&
    (rows.length == basis.length && rows.all (fun rs => rs.length == basis.length)) &&
    (List.finRange basis.length).all (fun i =>
      (List.finRange basis.length).all (fun j =>
        pair basis basis[i] basis[j] (pairRows rows i.val j.val)))

end Macaulean.Algebra.GroebnerCertificates
