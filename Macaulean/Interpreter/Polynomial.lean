import Macaulean.Polynomial.Basic

/-!
# Rational polynomials for the M2 runtime

The representation and arithmetic are the existing `Macaulean.Polynomial Rat n`.
The runtime wrapper supplies a generative ring identity and variable names. It
never conflates separately constructed rings merely because their names agree.
Every public arithmetic result is normalized before leading terms are observed.
There is deliberately no polynomial reduction or Groebner algorithm here.
-/
namespace Macaulean.M2.Algebra

inductive CoefficientRing where
  | integers | rationals
  deriving Repr, DecidableEq, Inhabited

structure Ring where
  id : Nat
  names : List String
  deriving Repr, DecidableEq, Inhabited

def Ring.toM2String (r : Ring) : String :=
  "QQ[" ++ ", ".intercalate r.names ++ "]"

structure Poly where
  ring : Ring
  data : Macaulean.Polynomial Rat ring.names.length
  deriving Repr, Inhabited

instance : DecidableEq Poly := fun p q => by
  cases p with
  | mk r a =>
    cases q with
    | mk s b =>
      by_cases h : r = s
      · subst s
        exact decidable_of_iff (a = b) (by simp only [Poly.mk.injEq])
      · exact isFalse (by intro e; cases e; exact h rfl)

namespace Poly

def ofData (r : Ring) (p : Macaulean.Polynomial Rat r.names.length) : Poly :=
  ⟨r, p.normalize⟩

def constant (r : Ring) (c : Rat) : Poly :=
  ofData r ⟨[⟨c, Macaulean.Mon.unit⟩]⟩

def variable (r : Ring) (i : Nat) : Poly :=
  ofData r ⟨[⟨1, ⟨(List.range r.names.length).map (fun j => if i = j then 1 else 0), by simp⟩⟩]⟩

/-- A checked data boundary, also used by independent native test decoders. -/
def ofTerms (r : Ring) (ts : List (List Nat × Rat)) : Option Poly := do
  let terms ← ts.mapM fun (powers, coefficient) => do
    if h : powers.length = r.names.length then
      return (⟨coefficient, ⟨powers, h⟩⟩ : Macaulean.PolyTerm Rat r.names.length)
    else none
  return ofData r ⟨terms⟩

def dataIn (p : Poly) (r : Ring) : Option (Macaulean.Polynomial Rat r.names.length) :=
  if h : p.ring = r then
    some (cast (congrArg (fun r : Ring => Macaulean.Polynomial Rat r.names.length) h) p.data)
  else none

def add (p q : Poly) : Option Poly := do
  let b ← q.dataIn p.ring
  return ofData p.ring (p.data.add b)

def neg (p : Poly) : Poly := ofData p.ring p.data.neg

def sub (p q : Poly) : Option Poly := p.add q.neg

def mul (p q : Poly) : Option Poly := do
  let b ← q.dataIn p.ring
  return ofData p.ring (p.data.mul b)

def smul (c : Rat) (p : Poly) : Poly := ofData p.ring (p.data.smul c)

def pow (p : Poly) (n : Nat) : Poly := ofData p.ring (p.data.pow n)

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

/-- Divisibility here is only for nonzero single-term polynomials over QQ. -/
def monomialDivides (a b : Poly) : Option Bool := do
  if a.ring != b.ring then none else do
    let a ← a.monomial?
    let b ← b.monomial?
    return (a.monomial.powers.zip b.monomial.powers).all fun (i,j) => i ≤ j

/-- Exact monomial quotient; no general reduction is hidden in the backend. -/
def monomialQuotient (a b : Poly) : Option Poly := do
  let true ← monomialDivides b a | none
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
    let negative := t.coefficient < 0
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

/-- Rectangular polynomial data; only checked constructors are exposed to M2. -/
structure Matrix where
  ring : Ring
  columns : Nat
  rows : List (List Poly)
  deriving Repr, DecidableEq, Inhabited

/-- `representations[j][i]` expresses generator j in original input generator i.
The container records data, not a proposition asserting the Groebner criterion. -/
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
  | makeBasis | changeMatrix | basisInput
  deriving Repr, DecidableEq, Inhabited

def Primitive.bindings : List (String × Primitive) := [
  ("ideal", .ideal), ("gens", .gens), ("generators", .gens),
  ("entries", .entries), ("flatten", .flatten), ("ring", .ringOf), ("numgens", .numgens),
  ("leadCoefficient", .leadCoefficient), ("leadMonomial", .leadMonomial),
  ("leadTerm", .leadTerm), ("exponents", .exponents), ("listForm", .listForm), ("terms", .terms),
  ("promote", .promote), ("numerator", .numerator), ("denominator", .denominator), ("size", .size),
  ("m2MonomialDivides", .monomialDivides), ("m2MonomialQuotient", .monomialQuotient),
  ("m2MonomialLCM", .monomialLCM), ("m2MonomialCompare", .monomialCompare),
  ("m2MakeBasis", .makeBasis), ("getChangeMatrix", .changeMatrix), ("m2BasisInput", .basisInput)
]
end Macaulean.M2.Algebra
