import Macaulean.Interpreter.GCD.Univariate
import Macaulean.Interpreter.Polynomials

/-! Bridges from the actual DSL operators to the canonical univariate arithmetic.
The ring identity and generator name are arbitrary; no example input is baked
into these statements. -/
namespace Macaulean.M2.GCD.Univariate
open Macaulean KernelPolynomial

def ringInfo (id : Nat) (name : String) : Polynomials.RingInfo := ⟨id,[name]⟩

def value (id : Nat) (name : String) (p : Poly) : Value :=
  .algebra (.poly (ringInfo id name) (Polynomials.encode p))

theorem mul_canonical (p q : Poly) : Canonical (KernelPolynomial.mul p q).terms :=
  normalize_canonical _

theorem eval_sub (id : Nat) (name : String) (p q : Poly)
    (hp : Canonical p.terms) (hq : Canonical q.terms) :
    evalBinOp .sub (value id name p) (value id name q) =
      .ok (value id name (KernelPolynomial.sub p q)) := by
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.common,
    Polynomials.polyRing?, Polynomials.cast, Polynomials.arithmetic,
    Polynomials.sub, Polynomials.binary_bridge, Polynomials.normalize_bridge,
    normalize_eq_self p hp, normalize_eq_self q hq,
    normalize_eq_self _ (sub_canonical p q),
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem eval_mul (id : Nat) (name : String) (p q : Poly)
    (hp : Canonical p.terms) (hq : Canonical q.terms) :
    evalBinOp .mul (value id name p) (value id name q) =
      .ok (value id name (KernelPolynomial.mul p q)) := by
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.common,
    Polynomials.polyRing?, Polynomials.cast, Polynomials.arithmetic,
    Polynomials.matrixView?, Polynomials.mul_bridge, Polynomials.normalize_bridge,
    normalize_eq_self p hp, normalize_eq_self q hq,
    normalize_eq_self _ (mul_canonical p q),
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem as_polynomial (id : Nat) (name : String) (p : Poly)
    (hp : Canonical p.terms) :
    Polynomials.asPolynomial (value id name p) =
      .ok (ringInfo id name, Polynomials.encode p) := by
  simp [value, ringInfo, Polynomials.asPolynomial, Polynomials.normalize_bridge,
    normalize_eq_self p hp, Polynomials.liftError, Except.mapError,
    bind, Except.bind, pure, Except.pure]

theorem leading_coefficient (id : Nat) (name : String) (t : Term) (ts : List Term)
    (hp : Canonical (t :: ts)) :
    Polynomials.callPrimitive .leadCoefficient (value id name ⟨t :: ts⟩) =
      .ok (.qq t.coefficient) := by
  have harg : Polynomials.unaryArg (value id name ⟨t :: ts⟩) =
      .ok (value id name ⟨t :: ts⟩) := rfl
  simp only [Polynomials.callPrimitive, harg, bind, Except.bind, pure, Except.pure,
    as_polynomial id name ⟨t :: ts⟩ hp]
  rfl

theorem leading_monomial (id : Nat) (name : String) (t : Term) (ts : List Term)
    (hp : Canonical (t :: ts)) :
    Polynomials.callPrimitive .leadMonomial (value id name ⟨t :: ts⟩) =
      .ok (value id name (monomial 1 t.monomial.degree)) := by
  have harg : Polynomials.unaryArg (value id name ⟨t :: ts⟩) =
      .ok (value id name ⟨t :: ts⟩) := rfl
  simp only [Polynomials.callPrimitive, harg, bind, Except.bind, pure, Except.pure,
    as_polynomial id name ⟨t :: ts⟩ hp]
  simp only [Polynomials.encode, List.map_cons, List.head?_cons]
  rw [powers_singleton t.monomial]
  rfl

theorem leading_term (id : Nat) (name : String) (t : Term) (ts : List Term)
    (hp : Canonical (t :: ts)) :
    Polynomials.callPrimitive .leadTerm (value id name ⟨t :: ts⟩) =
      .ok (value id name ⟨[t]⟩) := by
  have harg : Polynomials.unaryArg (value id name ⟨t :: ts⟩) =
      .ok (value id name ⟨t :: ts⟩) := rfl
  simp only [Polynomials.callPrimitive, harg, bind, Except.bind, pure, Except.pure,
    as_polynomial id name ⟨t :: ts⟩ hp]
  rfl

theorem monomial_canonical (c : Rat) (k : Nat) (hc : c ≠ 0) :
    Canonical (monomial c k).terms :=
  .cons hc (below_nil _) .nil

theorem normalized_singleton (c : Rat) (k : Nat) (hc : c ≠ 0) :
    Polynomials.normalized 1 [(c,[k])] = .ok [(c,[k])] := by
  change Polynomials.normalized 1 (Polynomials.encode (monomial c k)) = _
  rw [Polynomials.normalize_bridge, normalize_eq_self _ (monomial_canonical c k hc)]
  rfl

theorem monomial_quotient (id : Nat) (name : String) (a b : Nat) (h : b ≤ a) :
    Polynomials.callPrimitive .monomialQuotient
      (.sequence [value id name (monomial 1 a), value id name (monomial 1 b)]) =
        .ok (value id name (monomial 1 (a-b))) := by
  simp [Polynomials.callPrimitive, Polynomials.binaryArgs, Polynomials.unpack,
    Polynomials.common, Polynomials.polyRing?, Polynomials.cast,
    Polynomials.monomialQuotient, Polynomials.monomial, Polynomials.divides,
    value, ringInfo, monomial, Polynomials.encode, normalized_singleton, h,
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]
  decide +kernel

theorem scalar_div (a b : Rat) (hb : b ≠ 0) :
    evalBinOp .div (.qq a) (.qq b) = .ok (.qq (a/b)) := by
  simp [evalBinOp, Value.toRat?, hb]

theorem monomial_divides (id : Nat) (name : String) (a b : Nat) :
    Polynomials.callPrimitive .monomialDivides
      (.sequence [value id name (monomial 1 a), value id name (monomial 1 b)]) =
        .ok (.bool (decide (a ≤ b))) := by
  simp [Polynomials.callPrimitive, Polynomials.binaryArgs, Polynomials.unpack,
    Polynomials.common, Polynomials.polyRing?, Polynomials.cast,
    Polynomials.monomial, Polynomials.divides,
    value, ringInfo, monomial, Polynomials.encode, normalized_singleton,
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem cancellationTerm_canonical {t u : Term} (ht : t.coefficient ≠ 0)
    (hu : u.coefficient ≠ 0) : Canonical (cancellationTerm t u).terms := by
  apply monomial_canonical
  intro hz
  have he := Rat.div_mul_cancel (a := t.coefficient) hu
  rw [hz, Rat.zero_mul] at he
  exact ht he.symm

/-- The exact production subtraction after forming the leading-term multiple
returns a canonical polynomial with a strictly lower degree bound. -/
theorem eval_cancellation (id : Nat) (name : String)
    (t u : Term) (ts us : List Term)
    (hp : Canonical (t :: ts)) (hq : Canonical (u :: us))
    (hdegree : u.monomial.degree ≤ t.monomial.degree) :
    ∃ out : Poly,
      evalBinOp .sub (value id name ⟨t :: ts⟩)
        (value id name (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)) =
          .ok (value id name out) ∧
      Canonical out.terms ∧ Below t.monomial.degree out.terms := by
  refine ⟨_, eval_sub id name _ _ hp (mul_canonical ..),
    sub_canonical .., cancellation_decreases hp hq hdegree⟩

end Macaulean.M2.GCD.Univariate
