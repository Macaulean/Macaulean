import Macaulean.Polynomial.Basic

/-!
# Sparse QQ polynomial data for the interpreter

Arithmetic uses the existing `Macaulean.Polynomial` implementation. The checked
first-order boundary validates exponent dimensions before constructing dependent
polynomials. Fresh session-relative ring identities distinguish isomorphic rings.
-/
namespace Macaulean.M2.Polynomials
abbrev Raw := List (Rat × List Nat)
structure RingInfo where
  id : Nat
  names : List String
  deriving Repr, DecidableEq, Inhabited

def RingInfo.display (r : RingInfo) : String := "QQ[" ++ ", ".intercalate r.names ++ "]"

def decodeTerms (n : Nat) : Raw → Except String (List (Macaulean.PolyTerm Rat n))
  | [] => .ok []
  | (c, powers) :: ts => do
    if h : powers.length = n then return ⟨c, ⟨powers, h⟩⟩ :: (← decodeTerms n ts)
    else .error "polynomial exponent vector has the wrong dimension"
def decode (n : Nat) (ts : Raw) : Except String (Macaulean.Polynomial Rat n) :=
  (fun terms => ⟨terms⟩) <$> decodeTerms n ts
def encode (p : Macaulean.Polynomial Rat n) : Raw :=
  p.terms.map fun t => (t.coefficient, t.monomial.powers)
def normalized (n : Nat) (ts : Raw) : Except String Raw := do
  return encode (Macaulean.Polynomial.normalize (← decode n ts))
def constant (n : Nat) (c : Rat) : Raw :=
  if c = 0 then [] else [(c, List.replicate n 0)]
def generator (n index : Nat) : Raw :=
  [(1, (List.range n).map fun i => if i = index then 1 else 0)]
def unary (n : Nat) (f : Macaulean.Polynomial Rat n → Macaulean.Polynomial Rat n)
    (p : Raw) : Except String Raw := do
  return encode (Macaulean.Polynomial.normalize (f (← decode n p)))
def binary (n : Nat)
    (f : Macaulean.Polynomial Rat n → Macaulean.Polynomial Rat n → Macaulean.Polynomial Rat n)
    (p q : Raw) : Except String Raw := do
  let p := Macaulean.Polynomial.normalize (← decode n p)
  let q := Macaulean.Polynomial.normalize (← decode n q)
  return encode (Macaulean.Polynomial.normalize (f p q))
def add (n : Nat) := binary n Macaulean.Polynomial.add
def sub (n : Nat) := binary n Macaulean.Polynomial.sub
def mul (n : Nat) := binary n Macaulean.Polynomial.mul
def neg (n : Nat) := unary n Macaulean.Polynomial.neg
def smul (n : Nat) (c : Rat) := unary n (Macaulean.Polynomial.smul c)
def pow (n : Nat) (p : Raw) (k : Nat) : Except String Raw := do
  let p := Macaulean.Polynomial.normalize (← decode n p)
  return encode (Macaulean.Polynomial.normalize (Macaulean.Polynomial.pow p k))

/-- Componentwise divisibility, never silently truncating mismatched dimensions. -/
def divides (a b : List Nat) : Bool :=
  a.length == b.length && (a.zip b).all (fun (i,j) => i ≤ j)
def monomial (n : Nat) (p : Raw) : Except String (Rat × List Nat) := do
  match ← normalized n p with
  | [t] => return t
  | _ => .error "expected a nonzero single-term polynomial"
def monomialQuotient (n : Nat) (numerator denominator : Raw) : Except String Raw := do
  let (a, x) ← monomial n numerator
  let (b, y) ← monomial n denominator
  if divides y x then return [(a / b, (x.zip y).map fun (i,j) => i-j)]
  else .error "monomial does not divide the numerator"
def monomialLCM (n : Nat) (p q : Raw) : Except String Raw := do
  let (_, x) ← monomial n p
  let (_, y) ← monomial n q
  return [(1, (x.zip y).map fun (i,j) => max i j)]
def monomialCompare (n : Nat) (p q : Raw) : Except String Int := do
  let (_, x) ← monomial n p
  let (_, y) ← monomial n q
  if hx : x.length = n then
    if hy : y.length = n then
      return match (Macaulean.Mon.grevlex ⟨x,hx⟩ ⟨y,hy⟩) with
        | .lt => -1 | .eq => 0 | .gt => 1
    else .error "invalid monomial dimension"
  else .error "invalid monomial dimension"

/-- Single-term division only; no general normal-form algorithm is hidden here. -/
def divideByTerm (n : Nat) (p q : Raw) : Except String (Raw × Raw) := do
  let (c, powers) ← monomial n q
  let p ← normalized n p
  let quotient := p.filterMap fun (d, exps) =>
    if divides powers exps then some (d/c, (exps.zip powers).map fun (i,j) => i-j) else none
  let remainder := p.filter fun (_,exps) => !divides powers exps
  return (quotient, remainder)

inductive Primitive where
  | leadCoefficient | leadMonomial | leadTerm | exponents | terms | listForm | size
  | ring | coefficientRing | generators | entries | numgens | ideal | promote | coefficient
  | monomialDivides | monomialQuotient | monomialLCM | monomialCompare | fromExponents
  deriving Repr, DecidableEq, Inhabited

def Primitive.name : Primitive → String
  | .leadCoefficient => "leadCoefficient" | .leadMonomial => "leadMonomial"
  | .leadTerm => "leadTerm" | .exponents => "exponents" | .terms => "terms"
  | .listForm => "listForm" | .size => "size" | .ring => "ring"
  | .coefficientRing => "coefficientRing" | .generators => "generators"
  | .entries => "entries" | .numgens => "numgens" | .ideal => "ideal"
  | .promote => "promote" | .coefficient => "coefficient"
  | .monomialDivides => "m2MonomialDivides" | .monomialQuotient => "m2MonomialQuotient"
  | .monomialLCM => "m2MonomialLCM" | .monomialCompare => "m2MonomialCompare"
  | .fromExponents => "m2Monomial"
def primitives : List Primitive := [
  .leadCoefficient,.leadMonomial,.leadTerm,.exponents,.terms,.listForm,.size,
  .ring,.coefficientRing,.generators,.entries,.numgens,.ideal,.promote,.coefficient,
  .monomialDivides,.monomialQuotient,.monomialLCM,.monomialCompare,.fromExponents]

/-- `row` is a generator matrix, not a general matrix engine. -/
inductive Object where
  | rationals
  | ring (info : RingInfo)
  | poly (info : RingInfo) (terms : Raw)
  | ideal (info : RingInfo) (generators : List Raw)
  | row (info : RingInfo) (entries : List Raw)
  | builtin (primitive : Primitive)
  deriving Repr, DecidableEq, Inhabited

def Object.ring? : Object → Option RingInfo
  | .ring r | .poly r _ | .ideal r _ | .row r _ => some r | _ => none
def Object.className : Object → String
  | .rationals => "Type" | .ring _ => "PolynomialRing" | .poly r _ => r.display
  | .ideal .. => "Ideal" | .row .. => "Matrix" | .builtin _ => "FunctionClosure"
def monomialText (names : List String) (powers : List Nat) : String :=
  "*".intercalate ((names.zip powers).filterMap fun (x,n) =>
    if n = 0 then none else some (if n = 1 then x else s!"{x}^{n}"))
def termText (r : RingInfo) (t : Rat × List Nat) : String :=
  let (c, powers) := t
  let m := monomialText r.names powers
  let coeff := if c.den = 1 then toString c.num else s!"({c.num}/{c.den})"
  if m.isEmpty then coeff
  else if c = 1 then m else if c = -1 then "-" ++ m else coeff ++ "*" ++ m
def polynomialText (r : RingInfo) : Raw → String
  | [] => "0"
  | t :: ts => ts.foldl (fun s t =>
      if t.1 < 0 then s ++ " - " ++ termText r (-t.1,t.2)
      else s ++ " + " ++ termText r t) (termText r t)
def Object.toM2String : Object → String
  | .rationals => "QQ" | .ring r => r.display | .poly r ts => polynomialText r ts
  | .ideal r ps => "ideal(" ++ ", ".intercalate (ps.map (polynomialText r)) ++ ")"
  | .row r ps => "matrix{{" ++ ", ".intercalate (ps.map (polynomialText r)) ++ "}}"
  | .builtin p => p.name
end Macaulean.M2.Polynomials
