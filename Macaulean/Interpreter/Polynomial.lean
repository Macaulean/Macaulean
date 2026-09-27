import Macaulean.Polynomial.Basic

/-!
# Rational polynomials for the M2 runtime

The representation is `Macaulean.Polynomial Rat n`. The wrapper supplies
generative ring identity and variable bindings. Distinct ring constructions
are not conflated, even when their printed names agree.

Arithmetic uses normalization and structurally recursive list operations.
The existing backend's newer `mergeTerms`/`mulTerms` execute after compilation
but their definitions depend on Classical.choice; they must not sit on the
kernel-evaluation path. There is no reduction or Groebner algorithm here.
-/
namespace Macaulean.M2.Algebra

inductive CoefficientRing where
  | integers | rationals
  deriving Repr, DecidableEq, Inhabited

structure Ring where
  id : Nat
  names : List String
  /-- None denotes the global symbol; Some denotes an explicitly quoted local cell. -/
  cells : List (Option Nat) := []
  deriving Repr, DecidableEq, Inhabited

def Ring.toM2String (r : Ring) : String :=
  "QQ[" ++ ", ".intercalate r.names ++ "]"

structure Poly where
  ring : Ring
  data : Macaulean.Polynomial Rat ring.names.length
  deriving Repr, Inhabited

/-- A nondependent view for deciding equality without transporting polynomial data. -/
def Poly.termData (p : Poly) : List (Rat × List Nat) :=
  p.data.terms.map fun t => (t.coefficient, t.monomial.powers)

private theorem termData_injective {n : Nat} (a b : Macaulean.PolyTerm Rat n)
    (h : (a.coefficient, a.monomial.powers) = (b.coefficient, b.monomial.powers)) : a = b := by
  rcases a with ⟨a, ⟨xs, hx⟩⟩
  rcases b with ⟨b, ⟨ys, hy⟩⟩
  rcases Prod.mk.inj h with ⟨rfl, rfl⟩
  rfl

private theorem termsData_injective {n : Nat} (xs ys : List (Macaulean.PolyTerm Rat n))
    (h : xs.map (fun t => (t.coefficient, t.monomial.powers)) =
      ys.map (fun t => (t.coefficient, t.monomial.powers))) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hxy := termData_injective x y h.1
      have htail := ih ys h.2
      cases hxy
      cases htail
      rfl

private theorem Poly.eq_iff_data (p q : Poly) :
    (p.ring = q.ring ∧ p.termData = q.termData) ↔ p = q := by
  constructor
  · rintro ⟨hr, ht⟩
    rcases p with ⟨r, ⟨xs⟩⟩
    rcases q with ⟨s, ⟨ys⟩⟩
    change r = s at hr
    subst s
    have h := termsData_injective xs ys ht
    cases h
    rfl
  · intro h
    cases h
    exact ⟨rfl, rfl⟩

instance : DecidableEq Poly := fun p q =>
  decidable_of_iff (p.ring = q.ring ∧ p.termData = q.termData) (Poly.eq_iff_data p q)

/-! First-order, total arithmetic in the existing polynomial representation.
Normalization does not assume its input is sorted or free of zero terms. -/
namespace KernelPolynomial

def add (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  (⟨p.terms ++ q.terms⟩ : Macaulean.Polynomial Rat n).normalize

def mul (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  (⟨p.terms.flatMap fun t =>
    Macaulean.Polynomial.mulMonTerms t.coefficient t.monomial q.terms⟩ :
    Macaulean.Polynomial Rat n).normalize

def pow (p : Macaulean.Polynomial Rat n) : Nat → Macaulean.Polynomial Rat n
  | 0 => ⟨[⟨1, Macaulean.Mon.unit⟩]⟩
  | k + 1 => mul p (pow p k)

end KernelPolynomial

namespace Poly

def ofData (r : Ring) (p : Macaulean.Polynomial Rat r.names.length) : Poly :=
  ⟨r, p.normalize⟩

def constant (r : Ring) (c : Rat) : Poly :=
  ofData r ⟨[⟨c, Macaulean.Mon.unit⟩]⟩

def indeterminate (r : Ring) (i : Nat) : Poly :=
  ofData r ⟨[⟨1, ⟨(List.range r.names.length).map (fun j => if i = j then 1 else 0), by simp⟩⟩]⟩

/-- A checked data boundary, also used by independent native test decoders. -/
def ofTerms (r : Ring) (ts : List (List Nat × Rat)) : Option Poly := do
  let terms ← ts.mapM fun (powers, coefficient) => do
    if h : powers.length = r.names.length then
      return (⟨coefficient, ⟨powers, h⟩⟩ : Macaulean.PolyTerm Rat r.names.length)
    else none
  return ofData r ⟨terms⟩

/-- Transport only the erased length proof, never the computational polynomial. -/
def dataIn (p : Poly) (r : Ring) : Option (Macaulean.Polynomial Rat r.names.length) :=
  if h : p.ring = r then
    some ⟨p.data.terms.map fun t => ⟨t.coefficient,
      ⟨t.monomial.powers, t.monomial.powers_length.trans
        (congrArg (fun s : Ring => s.names.length) h)⟩⟩⟩
  else none

def add (p q : Poly) : Option Poly := do
  let b ← q.dataIn p.ring
  return ⟨p.ring, KernelPolynomial.add p.data b⟩

def neg (p : Poly) : Poly := ofData p.ring p.data.neg

def sub (p q : Poly) : Option Poly := p.add q.neg

def mul (p q : Poly) : Option Poly := do
  let b ← q.dataIn p.ring
  return ⟨p.ring, KernelPolynomial.mul p.data b⟩

def smul (c : Rat) (p : Poly) : Poly := ofData p.ring (p.data.smul c)

def pow (p : Poly) (n : Nat) : Poly := ⟨p.ring, KernelPolynomial.pow p.data n⟩

def isZero (p : Poly) : Bool := p.data.terms.isEmpty

def constant? (p : Poly) : Option Rat :=
  match p.data.terms with
  | [] => some 0
  | [t] => if t.monomial.powers.all (· == 0) then some t.coefficient else none
  | _ => none

def leadingCoefficient (p : Poly) : Rat :=
  match p.data.terms with | [] => 0 | t :: _ => t.coefficient

def leadingTerm (p : Poly) : Poly :=
  match p.data.terms with | [] => constant p.ring 0 | t :: _ => ofData p.ring ⟨[t]⟩

def leadingMonomial (p : Poly) : Poly :=
  match p.data.terms with
  | [] => constant p.ring 0
  | t :: _ => ofData p.ring ⟨[⟨1, t.monomial⟩]⟩

def monomial? (p : Poly) : Option (Macaulean.PolyTerm Rat p.ring.names.length) :=
  match p.data.terms with | [t] => some t | _ => none

/-- Recover the symbol of an existing indeterminate, including its local binding. -/
def indeterminate? (p : Poly) : Option (String × Option Nat) := do
  let t ← p.monomial?
  if t.coefficient != 1 || t.monomial.degree != 1 then none else do
    let i := t.monomial.powers.idxOf 1
    let name ← p.ring.names[i]?
    return (name, (p.ring.cells[i]?).getD none)

def monomialDivides (a b : Poly) : Option Bool := do
  if a.ring != b.ring then none else do
    let a ← a.monomial?
    let b ← b.monomial?
    return (a.monomial.powers.zip b.monomial.powers).all fun (i,j) => i ≤ j

/-- Exact monomial quotient; no general reduction is hidden in the backend. -/
def monomialQuotient (a b : Poly) : Option Poly := do
  if !(← monomialDivides b a) then none else do
    let x ← a.monomial?
    let y ← b.monomial?
    ofTerms a.ring [(List.zipWith (· - ·) x.monomial.powers y.monomial.powers,
      x.coefficient / y.coefficient)]

def monomialLCM (a b : Poly) : Option Poly := do
  if a.ring != b.ring then none else do
    let x ← a.monomial?
    let y ← b.monomial?
    ofTerms a.ring [(List.zipWith max x.monomial.powers y.monomial.powers, 1)]

def leadingCompare (a b : Poly) : Option Ordering := do
  let b ← b.dataIn a.ring
  match a.data.terms, b.terms with
  | [], [] => return .eq
  | [], _ => return .lt
  | _, [] => return .gt
  | x :: _, y :: _ => return x.monomial.grevlex y.monomial

private def monomialString (names : List String) (powers : List Nat) : String :=
  "*".intercalate ((names.zip powers).filterMap fun (name,n) =>
    if n = 0 then none else if n = 1 then some name else some s!"{name}^{n}")

private def unsignedTerm (names : List String) (c : Rat) (powers : List Nat) : String :=
  let monomial := monomialString names powers
  let coefficient := if c.den = 1 then toString c.num else s!"({c.num}/{c.den})"
  if monomial.isEmpty then coefficient
  else if c = 1 then monomial else coefficient ++ "*" ++ monomial

def toM2String (p : Poly) : String :=
  let parts := p.data.terms.map fun t =>
    let negative : Bool := decide (t.coefficient < 0)
    let c := if negative then -t.coefficient else t.coefficient
    (negative, unsignedTerm p.ring.names c t.monomial.powers)
  match parts with
  | [] => "0"
  | (negative, head) :: tail =>
    (if negative then "-" else "") ++ head ++
      String.join (tail.map fun (neg, body) => (if neg then " - " else " + ") ++ body)
end Poly

structure Ideal where
  ring : Ring
  generators : List Poly
  deriving Repr, DecidableEq, Inhabited

structure Matrix where
  ring : Ring
  columns : Nat
  rows : List (List Poly)
  deriving Repr, DecidableEq, Inhabited

/-- Row j expresses generator j in the original input generators.
This is data, not a proposition asserting the Groebner criterion. -/
structure Basis where
  input : Ideal
  generators : List Poly
  representations : List (List Poly)
  deriving Repr, DecidableEq, Inhabited

inductive Primitive where
  | ideal | gens | entries | flatten | ringOf | numgens
  | leadCoefficient | leadMonomial | leadTerm | exponents | listForm | terms
  | promote | numerator | denominator | size
  | monomialDivides | monomialQuotient | monomialLCM | monomialCompare
  | makeBasis | changeMatrix | basisInput | generatorList | asIdeal
  deriving Repr, DecidableEq, Inhabited

def Primitive.bindings : List (String × Primitive) := [
  ("ideal", .ideal), ("gens", .gens), ("generators", .gens),
  ("entries", .entries), ("flatten", .flatten), ("ring", .ringOf), ("numgens", .numgens),
  ("leadCoefficient", .leadCoefficient), ("leadMonomial", .leadMonomial),
  ("leadTerm", .leadTerm), ("exponents", .exponents), ("listForm", .listForm), ("terms", .terms),
  ("promote", .promote), ("numerator", .numerator), ("denominator", .denominator), ("size", .size),
  ("m2MonomialDivides", .monomialDivides), ("m2MonomialQuotient", .monomialQuotient),
  ("m2MonomialLCM", .monomialLCM), ("m2MonomialCompare", .monomialCompare),
  ("m2MakeBasis", .makeBasis), ("getChangeMatrix", .changeMatrix), ("m2BasisInput", .basisInput),
  ("m2GeneratorList", .generatorList), ("m2AsIdeal", .asIdeal)
]
end Macaulean.M2.Algebra
