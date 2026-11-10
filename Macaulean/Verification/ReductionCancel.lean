import Macaulean.Verification.ReductionCancelTail
import Macaulean.Verification.ReductionCoefficient

/-! Successful source cancellation, including both private assignments. -/
namespace Macaulean.M2.Verification.ReductionCancel
open Lexical Macaulean.M2.Runtime GCD.Execution Views ProofJobs.RuntimeReduction

/-- Expose the source assignments and coefficient evaluation in their original
order. This equality preserves errors as well as successful results. -/
theorem expose (fuel : Nat) (parent s : State)
    (pending row gs remainder j oldTerm oldDivisor oldCoefficient : Value)
    (hf : InFrame parent [pending,row,gs,remainder,j,oldTerm,oldDivisor,oldCoefficient] s) :
    eval (fuel+4) reductionCancel [frame parent 8] s =
      (show Except Signal (Value × State) from do
        let g ← liftResult (evalBinOp .index gs j)
        let selected ← liftResult (writeRef (.slot 0 6) g [frame parent 8] s)
        let (c,coefficientState) ← eval (fuel+1) reductionCoefficient [frame parent 8] selected
        let next ← liftResult (writeRef (.slot 0 7) c [frame parent 8] coefficientState)
        eval (fuel+2) reductionCancelRecurse [frame parent 8] next) := by
  have h2 := hf.read 2 gs rfl
  have h4 := hf.read 4 j rfl
  simp only [List.length_cons, List.length_nil] at h2 h4
  have assignment : eval (fuel+3) (.set (.slot 0 6) (.binop .index (localVar 2) (localVar 4)))
      [frame parent 8] s = (show Except Signal (Value × State) from do
        let g ← liftResult (evalBinOp .index gs j)
        let selected ← liftResult (writeRef (.slot 0 6) g [frame parent 8] s)
        pure (g,selected)) := by
    simp only [eval, localVar, checkWritable, h2, h4, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
    cases evalBinOp .index gs j <;> rfl
  unfold reductionCancel
  rw [eval, assignment]
  cases hi : evalBinOp .index gs j <;>
    simp only [liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  case ok g =>
    cases hw : writeRef (.slot 0 6) g [frame parent 8] s <;>
      simp only []
    case ok selected =>
      rw [eval]
      have setCoefficient : eval (fuel+2) (.set (.slot 0 7) reductionCoefficient)
          [frame parent 8] selected = (show Except Signal (Value × State) from do
            let (c,t) ← eval (fuel+1) reductionCoefficient [frame parent 8] selected
            let next ← liftResult (writeRef (.slot 0 7) c [frame parent 8] t)
            pure (c,next)) := by
        rw [eval]
        rfl
      rw [setCoefficient]
      cases hc : eval (fuel+1) reductionCoefficient [frame parent 8] selected <;>
        simp only [bind, Except.bind, pure, Except.pure]
      case ok pair =>
        rcases pair with ⟨c,t⟩
        cases hw7 : writeRef (.slot 0 7) c [frame parent 8] t <;>
          simp only [liftResult, Except.mapError]

private theorem exhausted (s : State) (fs : Frames) :
    eval 3 reductionCancel fs s = .error (.error .fuelExhausted) := by
  simp only [reductionCancel, eval, checkWritable, liftResult, Except.mapError,
    bind, Except.bind]

/-- Expose a strictly smaller recursive call and the executed row/arithmetic
updates, without requiring a representation invariant. -/
theorem successful_step (fuel : Nat) (parent s after : State) (result : Value)
    (coefficients : Row r n) (pending remainder : Views.Polynomial r)
    (reducers : List (RepresentedReducer r n)) (j oldTerm oldDivisor oldCoefficient : Value)
    (hf : InFrame parent [pending.value,coefficients.value,
      .list (reducers.map RepresentedReducer.value),remainder.value,j,oldTerm,oldDivisor,oldCoefficient] s)
    (globals : PreludeBindings parent)
    (success : catchReturn (eval fuel reductionCancel [frame parent 8] s) = .ok (result,after)) :
    ∃ (c product nextPending : Views.Polynomial r) (g : RepresentedReducer r n) (updated : Row r n) (next : State) (depth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      g ∈ reducers ∧
      PolynomialRows.Subtracts c coefficients.values g.coefficients.values updated.values ∧
      evalBinOp .mul c.value g.polynomial.value = .ok product.value ∧
      evalBinOp .sub pending.value product.value = .ok nextPending.value ∧
      call depth (.algebra (.library "m2gbReduce"))
        (.sequence [nextPending.value,updated.value,
          .list (reducers.map RepresentedReducer.value),remainder.value]) next = .ok (result,after) := by
  have bound : 4 ≤ fuel := by
    by_cases low : fuel ≤ 3
    · have hs := Fuel.preserves_success
        (Fuel.catchRefines (Fuel.eval_mono fuel (3-fuel) reductionCancel [frame parent 8] s)) success
      rw [Nat.add_sub_cancel' low, exhausted] at hs
      cases hs
    · omega
  obtain ⟨extra,rfl⟩ : ∃ extra, fuel = extra+4 := ⟨fuel-4,by omega⟩
  rw [expose extra parent s _ _ _ _ _ _ _ _ hf] at success
  cases hi : evalBinOp .index (.list (reducers.map RepresentedReducer.value)) j with
  | error e =>
    simp only [hi, liftResult, Except.mapError, bind, Except.bind, catchReturn] at success
    cases success
  | ok v =>
    obtain ⟨g,member,valueEq⟩ := ReductionTypes.selected_reducer reducers j v hi
    subst v
    obtain ⟨selected,hw6,hf6⟩ := hf.write 6 g.value (by simp)
    change writeRef (.slot 0 6) g.value [frame parent 8] s = .ok selected at hw6
    simp only [hi, liftResult, Except.mapError, bind, Except.bind, hw6] at success
    have h0 := hf6.read 0 pending.value rfl
    have h6 := hf6.read 6 g.value rfl
    simp only [List.length_set, List.length_cons, List.length_nil] at h0 h6
    have current := globals.of_env_eq hf6.env
    cases hc : eval (extra+1) reductionCoefficient [frame parent 8] selected with
    | error e =>
      cases e with
      | error e => simp only [hc, catchReturn] at success; cases success
      | returned v t =>
        exact False.elim (ReductionCoefficient.normal (extra+1) pending g.polynomial
          g.coefficients.value selected [frame parent 8] h0 h6 current v t hc)
    | ok pair =>
      rcases pair with ⟨v,t⟩
      obtain ⟨c,valueEq,stateEq⟩ := ReductionCoefficient.successful (extra+1) pending g.polynomial
        g.coefficients.value selected t [frame parent 8] v h0 h6 current (by rw [hc]; rfl)
      subst t
      subst v
      obtain ⟨next,hw7,hf7⟩ := hf6.write 7 c.value (by simp)
      change writeRef (.slot 0 7) c.value [frame parent 8] selected = .ok next at hw7
      simp only [hc, hw7] at success
      obtain ⟨product,np,updated,recursiveState,depth,smaller,bindings,rows,hm,hp,run⟩ :=
        ReductionCancelTail.successful_step (extra+2) parent next after result coefficients
          pending remainder c g (.list (reducers.map RepresentedReducer.value)) j oldTerm
          hf7 globals success
      exact ⟨c,product,np,g,updated,recursiveState,depth,by omega,bindings,member,rows,hm,hp,run⟩

/-- Every successful source cancellation exposes a strictly smaller recursive
call with the required representation invariant and protected bindings. -/
theorem successful (fuel : Nat) (parent s after : State) (result : Value)
    (generators coefficients : Row r n) (pending remainder : Views.Polynomial r)
    (reducers : List (RepresentedReducer r n)) (j oldTerm oldDivisor oldCoefficient : Value)
    (hf : InFrame parent [pending.value,coefficients.value,
      .list (reducers.map RepresentedReducer.value),remainder.value,j,oldTerm,oldDivisor,oldCoefficient] s)
    (globals : PreludeBindings parent)
    (input : InputInvariant generators pending remainder coefficients)
    (represented : ∀ g ∈ reducers, ReducerInvariant generators g)
    (success : catchReturn (eval fuel reductionCancel [frame parent 8] s) = .ok (result,after)) :
    ∃ (nextPending : Views.Polynomial r) (updated : Row r n) (next : State) (depth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      InputInvariant generators nextPending remainder updated ∧
      call depth (.algebra (.library "m2gbReduce"))
        (.sequence [nextPending.value,updated.value,
          .list (reducers.map RepresentedReducer.value),remainder.value]) next = .ok (result,after) := by
  obtain ⟨c,product,np,g,updated,next,depth,smaller,bindings,member,rows,hm,hp,run⟩ :=
    successful_step fuel parent s after result coefficients pending remainder reducers
      j oldTerm oldDivisor oldCoefficient hf globals success
  exact ⟨np,updated,next,depth,smaller,bindings,
    ReductionRow.invariant generators coefficients updated pending remainder c product np g
      input (represented g member) rows hm hp,run⟩

end Macaulean.M2.Verification.ReductionCancel
