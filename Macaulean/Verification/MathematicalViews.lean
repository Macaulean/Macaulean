import Macaulean.Algebra.PolynomialRing
import Macaulean.Interpreter.Polynomials

/-! Checked mathematical interpretations of actual worksheet objects. -/
namespace Macaulean.M2.Verification.MathematicalViews
open Macaulean.Algebra

/-- Export elaboration checks success and emits a theorem that the decoder
returned the export. The fallback is never evidence of successful decoding. -/
def extract [Inhabited α] : Except String α → α
  | .ok a => a | .error _ => default

def readField : Value → Except String CoefficientField
  | .algebra .rationals => .ok .rationals
  | .algebra (.finite (.field p)) =>
    if h : PrimeField.Valid p then .ok (.prime ⟨p,h⟩)
    else .error "coefficient field failed its inverse-law check"
  | _ => .error "mathematical export: expected a coefficient field"

def readRing : Value → Except String PolynomialRing
  | .algebra (.ring r) => .ok ⟨.rationals,r.id,r.names⟩
  | .algebra (.finite (.ring r)) =>
    if h : PrimeField.Valid r.offset then .ok ⟨.prime ⟨r.offset,h⟩,r.id,r.names⟩
    else .error "coefficient field failed its inverse-law check"
  | _ => .error "mathematical export: expected a polynomial ring"

def fieldValue : CoefficientField → Value
  | .rationals => .algebra .rationals
  | .prime F => Finite.wrap (.field F.offset)

theorem field_roundtrip (F : CoefficientField) : readField (fieldValue F) = .ok F := by
  cases F with
  | rationals => rfl
  | prime F => simp [fieldValue, Finite.wrap, readField, F.valid]

def ringValue (r : PolynomialRing) : Value :=
  match r.coefficients with
  | .rationals => .algebra (.ring ⟨r.id,r.names⟩)
  | .prime F => Finite.wrap (.ring ⟨r.id,F.offset,r.names⟩)

def polynomialValue {r : PolynomialRing} (p : RingPolynomial r) : Value :=
  match r with
  | ⟨.rationals,id,names⟩ => .algebra (.poly ⟨id,names⟩ (Polynomials.encode p.data))
  | ⟨.prime F,id,names⟩ => Finite.wrap (.poly ⟨id,F.offset,names⟩ (FinitePolynomialData.encode p.data))

def readPolynomial (r : PolynomialRing) (v : Value) : Except String (RingPolynomial r) :=
  match r with
  | ⟨.rationals,id,names⟩ =>
    match v with
    | .algebra (.poly s raw) =>
      if s = ⟨id,names⟩ then RingPolynomial.mk <$> Polynomials.decode names.length raw
      else .error "polynomial view: foreign ring identity"
    | _ => .error "polynomial view: incompatible coefficient field or value"
  | ⟨.prime F,id,names⟩ =>
    match v with
    | .algebra (.finite (.poly s raw)) =>
      if s = ⟨id,F.offset,names⟩ then RingPolynomial.mk <$> FinitePolynomialData.decode F.offset names.length raw
      else .error "polynomial view: foreign ring identity"
    | _ => .error "polynomial view: incompatible coefficient field or value"

def readPolynomials (r : PolynomialRing) : List Value → Except String (List (RingPolynomial r))
  | [] => .ok []
  | v::vs => do return (← readPolynomial r v) :: (← readPolynomials r vs)

def idealValue {r : PolynomialRing} (I : IdealPresentation r) : Value :=
  match r with
  | ⟨.rationals,id,names⟩ =>
    .algebra (.ideal ⟨id,names⟩ (I.generators.map fun p => Polynomials.encode p.data))
  | ⟨.prime F,id,names⟩ =>
    Finite.wrap (.ideal ⟨id,F.offset,names⟩ (I.generators.map fun p => FinitePolynomialData.encode p.data))

def readIdeal (r : PolynomialRing) (v : Value) : Except String (IdealPresentation r) := do
  let values ← match r,v with
    | ⟨.rationals,id,names⟩, .algebra (.ideal s gs) =>
      if s = ⟨id,names⟩ then .ok (gs.map fun p => .algebra (.poly s p))
      else .error "ideal view: foreign ring identity"
    | ⟨.prime F,id,names⟩, .algebra (.finite (.ideal s gs)) =>
      if s = ⟨id,F.offset,names⟩ then .ok (gs.map fun p => Finite.wrap (.poly s p))
      else .error "ideal view: foreign ring identity"
    | _,_ => .error "ideal view: incompatible coefficient field or value"
  return ⟨← readPolynomials r values⟩

theorem ring_roundtrip (r : PolynomialRing) : readRing (ringValue r) = .ok r := by
  rcases r with ⟨c,id,names⟩
  cases c with
  | rationals => rfl
  | prime F => simp [ringValue,Finite.wrap,readRing,F.valid]

set_option backward.isDefEq.respectTransparency false in
theorem polynomial_roundtrip {r : PolynomialRing} (p : RingPolynomial r) :
    readPolynomial r (polynomialValue p) = .ok p := by
  rcases r with ⟨c,id,names⟩
  cases c <;> cases p <;>
    simp [readPolynomial, polynomialValue,Finite.wrap,Polynomials.decode_encode,
      FinitePolynomialData.decode_encode,Functor.map,Except.map]

theorem polynomials_roundtrip (ps : List (RingPolynomial r)) :
    readPolynomials r (ps.map polynomialValue) = .ok ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [readPolynomials,polynomial_roundtrip,ih,bind,Except.bind,pure,Except.pure]

theorem ideal_roundtrip {r : PolynomialRing} (I : IdealPresentation r) :
    readIdeal r (idealValue I) = .ok I := by
  rcases r with ⟨c,id,names⟩
  cases c <;> cases I with
  | mk gs =>
    simp only [readIdeal,idealValue,Finite.wrap,List.map_map]
    change (do return IdealPresentation.mk (← readPolynomials _ (gs.map polynomialValue))) = _
    rw [polynomials_roundtrip]
    rfl

end Macaulean.M2.Verification.MathematicalViews
