import Macaulean.Interpreter.GCD.ReductionCorrectness

namespace Macaulean.M2.GCD.Univariate

def ringValue (id : Nat) (name : String) : Value := .algebra (.ring (ringInfo id name))

theorem promote_self (id : Nat) (name : String) (p : Poly) (hp : Canonical p.terms) :
    Polynomials.callPrimitive .promote (.sequence [value id name p,ringValue id name]) =
      .ok (value id name p) := by
  simp [Polynomials.callPrimitive, Polynomials.binaryArgs, Polynomials.unpack,
    value, ringInfo, ringValue, Polynomials.cast, Polynomials.normalize_bridge,
    normalize_eq_self p hp, Polynomials.liftError, Except.mapError,
    bind, Except.bind, pure, Except.pure]

theorem polynomial_ring (id : Nat) (name : String) (p : Poly) :
    Polynomials.callPrimitive .ring (value id name p) = .ok (ringValue id name) := rfl

theorem normal_form_data (id : Nat) (name : String) (p g : Poly)
    (hp : Canonical p.terms) (hg : Canonical g.terms) :
    Polynomials.callPrimitive .normalFormData
      (.sequence [value id name p,.list [value id name g]]) =
      .ok (.list [value id name p,.list [value id name g]]) := by
  simp [Polynomials.callPrimitive, Polynomials.binaryArgs, Polynomials.unpack,
    Polynomials.normalFormData, Polynomials.polyRing?, Polynomials.ringOf?,
    Polynomials.generatorValues, Polynomials.cast, value, ringInfo,
    Polynomials.normalize_bridge, normalize_eq_self p hp, normalize_eq_self g hg,
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem zero_mul_polynomial (id : Nat) (name : String) (p : Poly)
    (hp : Canonical p.terms) :
    evalBinOp .mul (.zz 0) (value id name p) = .ok (value id name ⟨[]⟩) := by
  have hz : ([] : Polynomials.Raw) = Polynomials.encode (⟨[]⟩ : Poly) := rfl
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.common,
    Polynomials.polyRing?, Polynomials.cast, Polynomials.scalar?, Polynomials.arithmetic,
    Polynomials.matrixView?, Polynomials.constant, hz, Polynomials.mul_bridge,
    Polynomials.normalize_bridge, normalize_eq_self p hp,
    normalize_eq_self (⟨[]⟩ : Poly) .nil,
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]
  rfl

end Macaulean.M2.GCD.Univariate
