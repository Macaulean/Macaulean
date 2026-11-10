import Macaulean.Verification.ReducerSelection
import Macaulean.Verification.IrreducibleArithmetic

/-! Connect the source selector's primitive checks to the coefficientwise
irreducibility view, retaining the actual ring and exponent dimension. -/
namespace Macaulean.M2.Verification.ReducerSelection
open Views

private theorem normalized_one (powers : List Nat) (dimension : powers.length = n) :
    Polynomials.normalized n [(1,powers)] = .ok [(1,powers)] := by
  simp [Polynomials.normalized, Polynomials.decode, Polynomials.decodeTerms,
    dimension, Polynomials.encode, KernelPolynomial.normalize, KernelPolynomial.insert,
    bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

private theorem leading_value (p : Views.Polynomial r) (t : Macaulean.PolyTerm Rat r.names.length)
    (ts : List (Macaulean.PolyTerm Rat r.names.length))
    (head : (KernelPolynomial.normalize p.data).terms = t :: ts) :
    Polynomials.callPrimitive .leadMonomial p.value =
      .ok (.algebra (.poly r [(1,t.monomial.powers)])) := by
  simp only [Polynomials.callPrimitive, Polynomials.unaryArg, Polynomials.unpack,
    Polynomials.asPolynomial, Polynomials.normalize_bridge, Polynomials.liftError,
    Except.mapError, Views.Polynomial.value, Views.Polynomial.raw,
    bind, Except.bind, pure, Except.pure]
  simp [Polynomials.encode, head]

private theorem divides_value (r : Polynomials.RingInfo) (a b : List Nat)
    (ha : a.length = r.names.length) (hb : b.length = r.names.length) :
    Polynomials.callPrimitive .monomialDivides
      (.sequence [.algebra (.poly r [(1,a)]),.algebra (.poly r [(1,b)])]) =
      .ok (.bool (Polynomials.divides a b)) := by
  simp [Polynomials.callPrimitive, Polynomials.binaryArgs, Polynomials.unpack,
    Polynomials.common, Polynomials.polyRing?, Polynomials.cast, Polynomials.monomial,
    normalized_one a ha, normalized_one b hb, Polynomials.liftError,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A rejected production divisibility check rules out divisibility of the
leading exponent vectors used in the mathematical view. -/
theorem test_false (pending divisor : Views.Polynomial r)
    (checked : test pending divisor = .ok (.bool false))
    (powers leading : List Nat) (hp : pending.leadingPowers? = some powers)
    (hg : divisor.leadingPowers? = some leading) :
    Polynomials.divides leading powers = false := by
  cases pterms : (KernelPolynomial.normalize pending.data).terms with
  | nil => simp [Views.Polynomial.leadingPowers?, pterms] at hp
  | cons p ps =>
    cases gterms : (KernelPolynomial.normalize divisor.data).terms with
    | nil => simp [Views.Polynomial.leadingPowers?, gterms] at hg
    | cons g gs =>
      have ep : p.monomial.powers = powers := by
        simpa [Views.Polynomial.leadingPowers?, pterms] using hp
      have eg : g.monomial.powers = leading := by
        simpa [Views.Polynomial.leadingPowers?, gterms] using hg
      simp only [test, leading_value pending p ps pterms, leading_value divisor g gs gterms,
        bind, Except.bind, divides_value r g.monomial.powers p.monomial.powers
          g.monomial.powers_length p.monomial.powers_length, Except.ok.injEq, Value.bool.injEq] at checked
      simpa [ep, eg] using checked

/-- The actual source selector's negative result makes the moved head irreducible. -/
theorem negative_leading_term (pending : Views.Polynomial r)
    (gs : List (ProofJobs.RuntimeReduction.RepresentedReducer r n))
    (s after : Runtime.State) (fuel : Nat) (result : Value)
    (globals : Runtime.PreludeBindings s)
    (run : Runtime.call fuel (.algebra (.library "m2gbReducer"))
      (.sequence [pending.value,.list (gs.map ProofJobs.RuntimeReduction.RepresentedReducer.value),.zz 0])
      s = .ok (result,after))
    (less : evalBinOp .lt result (.zz 0) = .ok (.bool true)) :
    Irreducible (Views.Polynomial.mk ⟨(KernelPolynomial.normalize pending.data).terms.take 1⟩)
      (gs.map ProofJobs.RuntimeReduction.RepresentedReducer.polynomial) := by
  apply IrreducibleArithmetic.leading_term
  intro powers head divisor member leading divisorHead
  obtain ⟨g,inReducers,rfl⟩ := List.mem_map.mp member
  obtain ⟨k,atIndex⟩ := List.mem_iff_getElem?.mp inReducers
  exact test_false pending g.polynomial
    (negative pending gs 0 (Nat.zero_le _) s after fuel result globals run less k (Nat.zero_le _) g atIndex)
    powers leading head divisorHead

end Macaulean.M2.Verification.ReducerSelection
