import Macaulean.Verification.ReductionRow
import Macaulean.Verification.ReductionEffects
import Macaulean.Verification.CallNormal

/-! The actual recursive tail of the cancellation branch. -/
namespace Macaulean.M2.Verification.ReductionCancelTail
open Lexical Macaulean.M2.Runtime GCD.Execution Views ProofJobs.RuntimeReduction

/-- Expose the actual row call and recursive reduction call, retaining their
original depths and preserving the caller's frame across the row helper. -/
theorem expose (fuel : Nat) (parent s : State)
    (pending remainder c product nextPending : Views.Polynomial r)
    (coefficients : Row r n) (g : RepresentedReducer r n)
    (gs j oldTerm : Value)
    (hf : InFrame parent
      [pending.value,coefficients.value,gs,remainder.value,j,oldTerm,g.value,c.value] s)
    (globals : PreludeBindings parent)
    (hm : evalBinOp .mul c.value g.polynomial.value = .ok product.value)
    (hp : evalBinOp .sub pending.value product.value = .ok nextPending.value) :
    eval (fuel+11) reductionCancelRecurse [frame parent 8] s =
      (show Except Signal (Value × State) from do
        let (row,next) ← call (fuel+6) (.algebra (.library "m2gbSubtractRow"))
          (.sequence [coefficients.value,c.value,g.coefficients.value,.zz 0]) s
        call (fuel+10) (.algebra (.library "m2gbReduce"))
          (.sequence [nextPending.value,row,gs,remainder.value]) next) := by
  have h0 := hf.read 0 pending.value rfl
  have h1 := hf.read 1 coefficients.value rfl
  have h6 := hf.read 6 g.value rfl
  have h7 := hf.read 7 c.value rfl
  simp only [List.length_cons, List.length_nil] at h0 h1 h6 h7
  have gr : readRef (.global "m2gbSubtractRow") [frame parent 8] s =
      .ok (.algebra (.library "m2gbSubtractRow")) := by
    have h := globals "m2gbSubtractRow" (by decide)
    simp only [readRef, hf.env, h]
    rfl
  have gc : readRef (.global "m2gbReduce") [frame parent 8] s =
      .ok (.algebra (.library "m2gbReduce")) := by
    have h := globals "m2gbReduce" (by decide)
    simp only [readRef, hf.env, h]
    rfl
  cases run : call (fuel+6) (.algebra (.library "m2gbSubtractRow"))
      (.sequence [coefficients.value,c.value,g.coefficients.value,.zz 0]) s with
  | error e =>
    simp only [reductionCancelRecurse, localVar, globalVar, eval, evalMany,
      h0, h1, h6, h7, gr, gc, RepresentedReducer.value, index_zero, index_one_pair,
      hm, hp, run, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  | ok pair =>
    rcases pair with ⟨row,next⟩
    have safe := ReductionEffects.row_safe (fuel+6)
      (.sequence [coefficients.value,c.value,g.coefficients.value,.zz 0]) s
      (globals.of_env_eq hf.env)
    simp only [run, ExecutionEffects.Safe] at safe
    have hn := hf.after_call safe
    have hn2 := hn.read 2 gs rfl
    have hn3 := hn.read 3 remainder.value rfl
    simp only [List.length_cons, List.length_nil] at hn2 hn3
    simp only [reductionCancelRecurse, localVar, globalVar, eval, evalMany,
      h0, h1, h6, h7, hn2, hn3, gr, gc, RepresentedReducer.value, index_zero, index_one_pair,
      hm, hp, run, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem exhausted (parent s : State)
    (pending remainder c product nextPending : Views.Polynomial r)
    (coefficients : Row r n) (g : RepresentedReducer r n)
    (gs j oldTerm : Value)
    (hf : InFrame parent
      [pending.value,coefficients.value,gs,remainder.value,j,oldTerm,g.value,c.value] s)
    (globals : PreludeBindings parent)
    (hm : evalBinOp .mul c.value g.polynomial.value = .ok product.value)
    (hp : evalBinOp .sub pending.value product.value = .ok nextPending.value) :
    eval 10 reductionCancelRecurse [frame parent 8] s = .error (.error .fuelExhausted) := by
  have h0 := hf.read 0 pending.value rfl
  have h1 := hf.read 1 coefficients.value rfl
  have h6 := hf.read 6 g.value rfl
  have h7 := hf.read 7 c.value rfl
  simp only [List.length_cons, List.length_nil] at h0 h1 h6 h7
  have gr : readRef (.global "m2gbSubtractRow") [frame parent 8] s =
      .ok (.algebra (.library "m2gbSubtractRow")) := by
    have h := globals "m2gbSubtractRow" (by decide)
    simp only [readRef, hf.env, h]
    rfl
  have gc : readRef (.global "m2gbReduce") [frame parent 8] s =
      .ok (.algebra (.library "m2gbReduce")) := by
    have h := globals "m2gbReduce" (by decide)
    simp only [readRef, hf.env, h]
    rfl
  simp only [reductionCancelRecurse, localVar, globalVar, eval, evalMany,
    h0, h1, h6, h7, gr, gc, RepresentedReducer.value, index_zero,
    hm, hp, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Expose a successful cancellation tail at its original budget, retaining
row subtraction and arithmetic facts without a representation hypothesis. -/
theorem successful_step (fuel : Nat) (parent s after : State) (result : Value)
    (coefficients : Row r n) (pending remainder c : Views.Polynomial r)
    (g : RepresentedReducer r n) (gs j oldTerm : Value)
    (hf : InFrame parent
      [pending.value,coefficients.value,gs,remainder.value,j,oldTerm,g.value,c.value] s)
    (globals : PreludeBindings parent)
    (success : catchReturn (eval fuel reductionCancelRecurse [frame parent 8] s) = .ok (result,after)) :
    ∃ (product nextPending : Views.Polynomial r) (updated : Row r n) (next : State) (depth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      PolynomialRows.Subtracts c coefficients.values g.coefficients.values updated.values ∧
      evalBinOp .mul c.value g.polynomial.value = .ok product.value ∧
      evalBinOp .sub pending.value product.value = .ok nextPending.value ∧
      call depth (.algebra (.library "m2gbReduce"))
        (.sequence [nextPending.value,updated.value,gs,remainder.value]) next = .ok (result,after) := by
  obtain ⟨product,hm,_⟩ := PolynomialArithmetic.eval_mul_coefficients c g.polynomial
  obtain ⟨np,hp,_⟩ := PolynomialArithmetic.eval_sub_coefficients pending product
  have bound : 11 ≤ fuel := by
    by_cases low : fuel ≤ 10
    · have hs := Fuel.preserves_success
        (Fuel.catchRefines (Fuel.eval_mono fuel (10-fuel) reductionCancelRecurse [frame parent 8] s)) success
      rw [Nat.add_sub_cancel' low,
        exhausted parent s pending remainder c product np coefficients g gs j oldTerm hf globals hm hp] at hs
      cases hs
    · omega
  obtain ⟨extra,rfl⟩ : ∃ extra, fuel = extra+11 := ⟨fuel-11,by omega⟩
  rw [expose extra parent s pending remainder c product np coefficients g gs j oldTerm hf globals hm hp] at success
  cases run : call (extra+6) (.algebra (.library "m2gbSubtractRow"))
      (.sequence [coefficients.value,c.value,g.coefficients.value,.zz 0]) s with
  | error e =>
    cases e with
    | error e => simp only [run, bind, Except.bind, catchReturn] at success; cases success
    | returned v t => exact False.elim (library_call_normal _ _ _ _ v t run)
  | ok pair =>
    rcases pair with ⟨row,next⟩
    have current := globals.of_env_eq hf.env
    have rowBinding : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")) :=
      current "m2gbSubtractRow" (by decide)
    obtain ⟨updated,valueEq,rows,effects⟩ := ReductionRow.successful_step coefficients c
      g.coefficients s next (extra+6) row rowBinding run
    simp only [run, bind, Except.bind] at success
    rw [(library_call_normal _ _ _ _).catchReturn_eq, valueEq] at success
    exact ⟨product,np,updated,next,extra+10,by omega,current.of_env_eq effects.env,rows,hm,hp,success⟩

/-- Invert any successful cancellation tail without increasing its recursive
budget, retaining the row dimension, representation invariant, and bindings. -/
theorem successful (fuel : Nat) (parent s after : State) (result : Value)
    (generators coefficients : Row r n) (pending remainder c : Views.Polynomial r)
    (g : RepresentedReducer r n) (gs j oldTerm : Value)
    (hf : InFrame parent
      [pending.value,coefficients.value,gs,remainder.value,j,oldTerm,g.value,c.value] s)
    (globals : PreludeBindings parent)
    (input : InputInvariant generators pending remainder coefficients)
    (reducer : ReducerInvariant generators g)
    (success : catchReturn (eval fuel reductionCancelRecurse [frame parent 8] s) = .ok (result,after)) :
    ∃ (nextPending : Views.Polynomial r) (updated : Row r n) (next : State) (depth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      InputInvariant generators nextPending remainder updated ∧
      call depth (.algebra (.library "m2gbReduce"))
        (.sequence [nextPending.value,updated.value,gs,remainder.value]) next = .ok (result,after) := by
  obtain ⟨product,np,updated,next,depth,smaller,bindings,rows,hm,hp,run⟩ :=
    successful_step fuel parent s after result coefficients pending remainder c g gs j oldTerm
      hf globals success
  exact ⟨np,updated,next,depth,smaller,bindings,
    ReductionRow.invariant generators coefficients updated pending remainder c product np g
      input reducer rows hm hp,run⟩

end Macaulean.M2.Verification.ReductionCancelTail
