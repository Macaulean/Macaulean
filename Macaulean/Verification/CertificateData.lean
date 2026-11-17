import Macaulean.Algebra.Certificates
import Macaulean.Verification.MathematicalViews

namespace Macaulean.M2.Verification.CertificateData
open Macaulean.Algebra MathematicalViews

/-- Check the concrete coefficient row against the exported mathematical ideal. -/
def checkMember (p : RingPolynomial r) (I : IdealPresentation r)
    (row : List (RingPolynomial r)) : Bool :=
  Certificates.represents p.data (I.generators.map RingPolynomial.data) (row.map RingPolynomial.data)

theorem checkMember_sound (p : RingPolynomial r) (I : IdealPresentation r)
    (row : List (RingPolynomial r)) (h : checkMember p I row = true) : I.Member p :=
  Certificates.represents_sound h

structure BasisPresentation (ring : PolynomialRing) where
  input : IdealPresentation ring
  output : IdealPresentation ring
  representations : List (List (RingPolynomial ring))

instance : Inhabited (BasisPresentation ring) := ⟨⟨default,default,[]⟩⟩

def readRows (r : PolynomialRing) : List (List Value) → Except String (List (List (RingPolynomial r)))
  | [] => .ok []
  | row::rows => do return (← readPolynomials r row) :: (← readRows r rows)

/-- A basis tag is decoded as an uncertified presentation, not a Gröbner theorem. -/
def readBasis (r : PolynomialRing) (value : Value) : Except String (BasisPresentation r) := do
  let (input,output,rows) ← match value with
    | .algebra (.basis s input output rows) =>
      .ok (.algebra (.ideal s input), .algebra (.ideal s output),
        rows.map fun row => row.map fun p => .algebra (.poly s p))
    | .algebra (.finite (.basis s input output rows)) =>
      .ok (Finite.wrap (.ideal s input), Finite.wrap (.ideal s output),
        rows.map fun row => row.map fun p => Finite.wrap (.poly s p))
    | _ => .error "certificate input must be a candidate basis"
  return ⟨← readIdeal r input, ← readIdeal r output, ← readRows r rows⟩

def checkIdealEquality (I : IdealPresentation r) (G : BasisPresentation r)
    (reverseRows : List (List (RingPolynomial r))) : Bool :=
  Certificates.sameIdeal (I.generators.map RingPolynomial.data)
    (G.output.generators.map RingPolynomial.data)
    (G.representations.map fun row => row.map RingPolynomial.data)
    (reverseRows.map fun row => row.map RingPolynomial.data)

theorem checkIdealEquality_sound (I : IdealPresentation r) (G : BasisPresentation r)
    (reverseRows : List (List (RingPolynomial r)))
    (h : checkIdealEquality I G reverseRows = true) : Ideal.Same I.meaning G.output.meaning :=
  Certificates.sameIdeal_sound h

/-- Candidate row generation uses the existing source-language reduction. Its
correctness is not assumed: `checkMember` checks its returned data independently.
In particular an altered library environment cannot manufacture a false proof. -/
def generateRow (fuel : Nat) (polynomial ideal : Value) (state : Runtime.State) :
    Except String (List Value) := do
  let gens ← (Polynomials.callPrimitive .generatorList ideal).mapError toString
  let .list generators := gens | .error "expected an ideal generator list"
  let zero ← (evalBinOp .mul (.zz 0) polynomial).mapError toString
  let (basis,state) ← (Runtime.finish (Runtime.call fuel (.algebra (.library "m2gbMain"))
    ideal state)).mapError toString
  let pairs ← match basis with
    | .algebra (.basis r _ gs rows) =>
      if gs.length != rows.length then .error "basis has invalid representation dimensions"
      else .ok (.list ((gs.zip rows).map fun (g,row) =>
        .list [.algebra (.poly r g),.list (row.map fun p => .algebra (.poly r p))]))
    | .algebra (.finite (.basis r _ gs rows)) =>
      if gs.length != rows.length then .error "basis has invalid representation dimensions"
      else .ok (.list ((gs.zip rows).map fun (g,row) =>
        .list [Finite.wrap (.poly r g),.list (row.map fun p => Finite.wrap (.poly r p))]))
    | _ => .error "basis generation returned an invalid certificate shape"
  let (result,state) ← (Runtime.finish (Runtime.call fuel (.algebra (.library "m2gbReduce"))
    (.sequence [polynomial,.list (generators.map fun _ => zero),pairs,zero]) state)).mapError toString
  let .list [_,row] := result | .error "reduction returned an invalid certificate shape"
  let (result,_) ← (Runtime.finish (Runtime.call fuel (.algebra (.library "m2gbScaleRow"))
    (.sequence [.zz (-1),row,.zz 0]) state)).mapError toString
  let .list coefficients := result | .error "reduction returned an invalid coefficient row"
  return coefficients

/-- Reduce against the supplied generators, without recomputing a Gröbner basis.
This preserves the degree bounds of the reduction's coefficient rows. These rows
remain untrusted until the independent Gröbner checker accepts them. -/
def generateReductionRow (fuel : Nat) (polynomial ideal : Value) (state : Runtime.State) :
    Except String (List Value) := do
  let gens ← (Polynomials.callPrimitive .generatorList ideal).mapError toString
  let .list generators := gens | .error "expected an ideal generator list"
  let ring ← (Polynomials.callPrimitive .ring ideal).mapError toString
  let zero ← (evalBinOp .mul (.zz 0) polynomial).mapError toString
  let (pairs,state) ← (Runtime.finish (Runtime.call fuel (.algebra (.library "m2gbInitial"))
    (.sequence [gens,ring,.zz 0]) state)).mapError toString
  let (result,state) ← (Runtime.finish (Runtime.call fuel (.algebra (.library "m2gbReduce"))
    (.sequence [polynomial,.list (generators.map fun _ => zero),pairs,zero]) state)).mapError toString
  let .list [_,row] := result | .error "reduction returned an invalid certificate shape"
  let (result,_) ← (Runtime.finish (Runtime.call fuel (.algebra (.library "m2gbScaleRow"))
    (.sequence [.zz (-1),row,.zz 0]) state)).mapError toString
  let .list coefficients := result | .error "reduction returned an invalid coefficient row"
  return coefficients

end Macaulean.M2.Verification.CertificateData
