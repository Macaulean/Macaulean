import Macaulean.Verification.ProofJobs.RuntimeReduction

/-! The old target is refuted by a kernel-checked runtime counterexample.
The corrected target excludes this state through an explicit binding invariant. -/
namespace Macaulean.M2.Verification.ProofJobs.RuntimeReduction.Counterexample
open Views
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
private def ring : Polynomials.RingInfo := ⟨9,[]⟩
private def one : Views.Polynomial ring := ⟨⟨[⟨1,⟨[],rfl⟩⟩]⟩⟩
private def zero : Views.Polynomial ring := ⟨⟨[]⟩⟩
private def gs : Row ring 1 := ⟨[one],rfl⟩
private def badState : Runtime.State :=
  { env := ("m2gbReduce",.closure 0)::prelude,
    heap := { functions := [.closure (.variadic "args") 1 (.int 7) []] } }
private def computation := Runtime.call 64 (.algebra (.library "m2gbReduce"))
  (.sequence [one.value,gs.value,.list [],zero.value]) badState

private theorem computation_success : ∃ after, computation = .ok (.zz 7,after) := by
  have result : computation.toOption.map Prod.fst = some (.zz 7) := by decide +kernel
  cases h : computation with
  | error e => simp [h, Except.toOption] at result
  | ok pair =>
    obtain ⟨v,s⟩ := pair
    simp [h, Except.toOption] at result
    subst v
    exact ⟨s,rfl⟩

private def UnrestrictedRepresentationStatement : Prop :=
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

theorem unrestricted_target_is_false : ¬ UnrestrictedRepresentationStatement := by
  intro claim
  have input : InputInvariant gs one zero gs := by
    intro powers
    simp only [one, zero, gs, Views.Polynomial.coeff,
      Views.Polynomial.raw, Polynomials.encode, List.map_cons, List.map_nil,
      coefficient_cons, coefficient_nil, linearCoefficient, productCoefficient,
      List.foldr_cons, List.foldr_nil, List.zip, List.zipWith, List.map_nil]
    split <;> grind
  obtain ⟨after,success⟩ := computation_success
  obtain ⟨rv,av,p,a,h,_⟩ := claim ring 1 gs one zero gs [] input
    (by simp) badState 64 (.zz 7) after success
  cases h
private def UnrestrictedIrreducibleStatement : Prop :=
  ∀ (r : Polynomials.RingInfo) (n : Nat) (pending remainder : Views.Polynomial r)
    (coefficients : Row r n) (reducers : List (RepresentedReducer r n)),
    Irreducible remainder (reducers.map RepresentedReducer.polynomial) →
    ∀ (s : Runtime.State) (fuel : Nat) (result : Value) (after : Runtime.State),
      Runtime.call fuel (.algebra (.library "m2gbReduce"))
        (.sequence [pending.value, coefficients.value,
          .list (reducers.map RepresentedReducer.value), remainder.value]) s = .ok (result,after) →
      ∃ rv av p, result = .list [rv,av] ∧ readPolynomial r rv = .ok p ∧
        Irreducible p (reducers.map RepresentedReducer.polynomial)

theorem unrestricted_irreducible_target_is_false : ¬ UnrestrictedIrreducibleStatement := by
  intro claim
  obtain ⟨after,success⟩ := computation_success
  obtain ⟨rv,av,p,h,_⟩ := claim ring 1 one zero gs []
    (by intro powers hn g hg; simp at hg) badState 64 (.zz 7) after success
  cases h

theorem badState_rejected : ¬ Runtime.PreludeBindings badState := by
  intro h
  have binding := h "m2gbReduce" (by decide +kernel)
  have wrong : badState.env.lookup "m2gbReduce" ≠ prelude.lookup "m2gbReduce" := by
    decide +kernel
  exact wrong binding

example : Runtime.PreludeBindings
    ({ env := ("userValue", .zz 5)::prelude } : Runtime.State) := by
  apply Runtime.PreludeBindings.initial.writeRef
    (ref := .global "userValue") (value := .zz 5) (frames := [])
  rfl

-- Concrete exported snapshots can discharge the hypothesis by computation.
example : Runtime.PreludeBindings ({} : Runtime.State) :=
  .of_check (by decide +kernel)
example : Runtime.checkPreludeBindings badState = false := by decide +kernel

open Lean Elab Command in
run_cmd do
  for name in [``Runtime.PreludeBindings.initial, ``Runtime.PreludeBindings.allocate,
      ``Runtime.PreludeBindings.function, ``Runtime.PreludeBindings.writeRef,
      ``Runtime.PreludeBindings.writeMany, ``Runtime.PreludeBindings.of_env_eq,
      ``Runtime.checkPreludeBindings_eq_true, ``Runtime.PreludeBindings.of_check,
      ``unrestricted_target_is_false, ``unrestricted_irreducible_target_is_false,
      ``badState_rejected] do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"
  logInfo "RUNTIME_ENVIRONMENT_COMPLETE: 11 axiom audits and both unrestricted targets refuted"

end Macaulean.M2.Verification.ProofJobs.RuntimeReduction.Counterexample
