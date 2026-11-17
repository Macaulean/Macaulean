import Macaulean.Verification.ViewLaws
import Macaulean.Verification.ProofJobs.Conservation
import Macaulean.Interpreter.Runtime

/-!
The exact generic represented-reduction target. It is a proposition definition,
not an axiom, theorem, proof placeholder or assumed primitive law. This target is
NOT yet discharged. It prevents an abstract conservation theorem from being
mistaken for a proof about the source-language implementation.
-/
namespace Macaulean.M2.Verification.ProofJobs.RuntimeReduction
open Views

structure RepresentedReducer (r : Polynomials.RingInfo) (n : Nat) where
  polynomial : Views.Polynomial r
  coefficients : Row r n

def RepresentedReducer.value (a : RepresentedReducer r n) : Value :=
  .list [a.polynomial.value, a.coefficients.value]

def InputInvariant (generators : Row r n) (pending remainder : Views.Polynomial r)
    (coefficients : Row r n) : Prop :=
  ∀ powers, pending.coeff powers + remainder.coeff powers =
    linearCoefficient coefficients.values generators.values powers

def ReducerInvariant (generators : Row r n) (g : RepresentedReducer r n) : Prop :=
  ∀ powers, g.polynomial.coeff powers =
    linearCoefficient g.coefficients.values generators.values powers

/-- The actual four-argument helper, not an incompatible two-argument contract. -/
def RepresentationStatement : Prop :=
  ∀ (r : Polynomials.RingInfo) (n : Nat) (generators : Row r n)
    (pending remainder : Views.Polynomial r) (coefficients : Row r n)
    (reducers : List (RepresentedReducer r n)),
    InputInvariant generators pending remainder coefficients →
    (∀ g ∈ reducers, ReducerInvariant generators g) →
    ∀ (s : Runtime.State) (fuel : Nat) (result : Value) (after : Runtime.State),
      Runtime.call fuel (.algebra (.library "m2gbReduce"))
        (.sequence [pending.value, coefficients.value,
          .list (reducers.map RepresentedReducer.value), remainder.value]) s = .ok (result,after) →
      ∃ (rv av : Value) (p : Views.Polynomial r) (a : Row r n),
        result = .list [rv,av] ∧ readPolynomial r rv = .ok p ∧ readRow r n av = .ok a ∧
        (∀ powers, p.coeff powers = linearCoefficient a.values generators.values powers)

/-- Separate from representation preservation, error-freedom and termination. -/
def IrreducibleStatement : Prop :=
  ∀ (r : Polynomials.RingInfo) (n : Nat) (pending remainder : Views.Polynomial r)
    (coefficients : Row r n) (reducers : List (RepresentedReducer r n)),
    Irreducible remainder (reducers.map RepresentedReducer.polynomial) →
    ∀ (s : Runtime.State) (fuel : Nat) (result : Value) (after : Runtime.State),
      Runtime.call fuel (.algebra (.library "m2gbReduce"))
        (.sequence [pending.value, coefficients.value,
          .list (reducers.map RepresentedReducer.value), remainder.value]) s = .ok (result,after) →
      ∃ rv av p, result = .list [rv,av] ∧ readPolynomial r rv = .ok p ∧
        Irreducible p (reducers.map RepresentedReducer.polynomial)

end Macaulean.M2.Verification.ProofJobs.RuntimeReduction
