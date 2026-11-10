import Macaulean.Verification.ReductionMove
import Macaulean.Verification.ReductionEffects

/-! Successful source dispatch into the two recursive reduction branches. -/
namespace Macaulean.M2.Verification.ReductionDispatch
open Lexical Macaulean.M2.Runtime GCD.Execution Views

/-- Expose only the selector and its private assignment, retaining the actual
branch syntax and original fuel. -/
theorem expose (fuel : Nat) (pending : Views.Polynomial r) (row gs remainder : Value)
    (s : State)
    (zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool false))
    (global : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer"))) :
    call (fuel+10) (.algebra (.library "m2gbReduce"))
      (.sequence [pending.value,row,gs,remainder]) s =
    catchReturn (show Except Signal (Value × State) from do
      let (j,selected) ← call (fuel+5) (.algebra (.library "m2gbReducer"))
        (.sequence [pending.value,gs,.zz 0])
        (s.allocate (reductionLocals pending.value row gs remainder)).2
      let next ← liftResult (writeRef (.slot 0 4) j [frame s 8] selected)
      eval (fuel+7) (.ifElse (.binop .lt (localVar 4) (.int 0))
        reductionMoveHead reductionCancel) [frame s 8] next) := by
  let vs := reductionLocals pending.value row gs remainder
  have h0 := allocated_read s vs 0 pending.value rfl
  have h2 := allocated_read s vs 2 gs rfl
  have hg := allocated_global s vs [(s.allocate vs).1] _ _ global
  rw [library_call (fuel+9) _ _ _ _ _ _ s reduction_source (by rfl)]
  change catchReturn (eval (fuel+9) reductionBody [(s.allocate vs).1] (s.allocate vs).2) = _
  have condition : eval (fuel+8) (.binop .eq (localVar 0) (.int 0))
      [(s.allocate vs).1] (s.allocate vs).2 = .ok (.bool false,(s.allocate vs).2) := by
    simp only [eval, localVar, h0, zero, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  unfold reductionBody
  rw [eval]
  simp only [condition, bind, Except.bind]
  rw [eval]
  have assignment : eval (fuel+7) (.set (.slot 0 4)
      (.apply (globalVar "m2gbReducer") (.sequence [localVar 0,localVar 2,.int 0])))
      [(s.allocate vs).1] (s.allocate vs).2 = (do
        let (j,selected) ← call (fuel+5) (.algebra (.library "m2gbReducer"))
          (.sequence [pending.value,gs,.zz 0]) (s.allocate vs).2
        let next ← liftResult (writeRef (.slot 0 4) j [frame s 8] selected)
        pure (j,next)) := by
    simp only [eval, evalMany, localVar, globalVar, h0, h2, hg, checkWritable,
      liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
    rfl
  rw [assignment]
  cases hs : call (fuel+5) (.algebra (.library "m2gbReducer"))
      (.sequence [pending.value,gs,.zz 0]) (s.allocate vs).2 with
  | error e => rfl
  | ok pair =>
    rcases pair with ⟨j,selected⟩
    cases hw : writeRef (.slot 0 4) j [frame s 8] selected <;>
      simp only [bind, Except.bind, pure, Except.pure, hw, liftResult, Except.mapError] <;> rfl

private theorem exhausted (pending : Views.Polynomial r) (row gs remainder : Value)
    (s : State)
    (zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool false))
    (global : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer"))) :
    call 9 (.algebra (.library "m2gbReduce"))
      (.sequence [pending.value,row,gs,remainder]) s = .error (.error .fuelExhausted) := by
  let vs := reductionLocals pending.value row gs remainder
  have h0 := allocated_read s vs 0 pending.value rfl
  have h2 := allocated_read s vs 2 gs rfl
  have hg := allocated_global s vs [(s.allocate vs).1] _ _ global
  rw [library_call 8 _ _ _ _ _ _ s reduction_source (by rfl)]
  change catchReturn (eval 8 reductionBody [(s.allocate vs).1] (s.allocate vs).2) = _
  simp only [reductionBody, localVar, globalVar, eval, evalMany,
    checkWritable, h0, h2, hg, zero,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

/-- A successful nonzero reduction reaches one of the tracked source branches
in a valid private frame, at strictly smaller fuel. -/
theorem successful_selected (fuel : Nat) (pending : Views.Polynomial r) (row gs remainder : Value)
    (s after : State) (result : Value)
    (globals : PreludeBindings s)
    (zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool false))
    (success : call fuel (.algebra (.library "m2gbReduce"))
      (.sequence [pending.value,row,gs,remainder]) s = .ok (result,after)) :
    ∃ (j : Value) (next : State) (negative : Bool) (depth : Nat) (selected : State) (selectorDepth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      InFrame s [pending.value,row,gs,remainder,j,.null,.null,.null] next ∧
      evalBinOp .lt j (.zz 0) = .ok (.bool negative) ∧
      call selectorDepth (.algebra (.library "m2gbReducer"))
        (.sequence [pending.value,gs,.zz 0])
        (s.allocate (reductionLocals pending.value row gs remainder)).2 = .ok (j,selected) ∧
      catchReturn (eval depth (if negative then reductionMoveHead else reductionCancel)
        [frame s 8] next) = .ok (result,after) := by
  have global : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer")) :=
    globals "m2gbReducer" (by decide)
  have bound : 10 ≤ fuel := by
    by_cases low : fuel ≤ 9
    · have hs := Fuel.preserves_success (Fuel.call_mono fuel (9-fuel) _ _ s) success
      rw [Nat.add_sub_cancel' low, exhausted pending row gs remainder s zero global] at hs
      cases hs
    · omega
  obtain ⟨extra, rfl⟩ : ∃ extra, fuel = extra+10 := ⟨fuel-10, by omega⟩
  rw [expose extra pending row gs remainder s zero global] at success
  let vs := reductionLocals pending.value row gs remainder
  let allocated := (s.allocate vs).2
  have normal := library_call_normal (extra+5) "m2gbReducer"
    (.sequence [pending.value,gs,.zz 0]) allocated
  cases hs : call (extra+5) (.algebra (.library "m2gbReducer"))
      (.sequence [pending.value,gs,.zz 0]) (s.allocate (reductionLocals pending.value row gs remainder)).2 with
  | error e =>
    cases e with
    | error e =>
      simp only [hs, bind, Except.bind, catchReturn] at success
      cases success
    | returned v t => exact False.elim (normal v t hs)
  | ok pair =>
    rcases pair with ⟨j,selected⟩
    have effects := ReductionEffects.selector_preserves (extra+5) _ j allocated selected
      (globals.allocate vs) hs
    have hf := (allocated_frame s vs).after_call effects
    obtain ⟨next, hw, hn⟩ := hf.write 4 j (by simp [vs, reductionLocals])
    change writeRef (.slot 0 4) j [frame s 8] selected = .ok next at hw
    simp only [hs, bind, Except.bind, hw, liftResult, Except.mapError] at success
    have h4 := hn.read 4 j (by simp [vs, reductionLocals])
    change readRef (.slot 0 4) [frame s 8] next = .ok j at h4
    have condition : eval (extra+6) (.binop .lt (localVar 4) (.int 0)) [frame s 8] next =
        (do let v ← liftResult (evalBinOp .lt j (.zz 0)); pure (v,next)) := by
      simp only [eval, localVar, h4, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
    rw [eval] at success
    simp only [condition, bind, Except.bind] at success
    cases cmp : evalBinOp .lt j (.zz 0) with
    | error e =>
      simp only [cmp, liftResult, Except.mapError, catchReturn] at success
      cases success
    | ok v =>
      simp only [cmp, liftResult, Except.mapError] at success
      cases v <;> try (simp only [catchReturn] at success; contradiction)
      case bool negative =>
        refine ⟨j,next,negative,extra+6,selected,extra+5,by omega,globals.of_env_eq hn.env,?_,cmp,hs,?_⟩
        · exact hn
        · cases negative <;> exact success

/-- A successful nonzero reduction reaches one of the tracked source branches
in a valid private frame, at strictly smaller fuel. -/
theorem successful (fuel : Nat) (pending : Views.Polynomial r) (row gs remainder : Value)
    (s after : State) (result : Value)
    (globals : PreludeBindings s)
    (zero : evalBinOp .eq pending.value (.zz 0) = .ok (.bool false))
    (success : call fuel (.algebra (.library "m2gbReduce"))
      (.sequence [pending.value,row,gs,remainder]) s = .ok (result,after)) :
    ∃ (j : Value) (next : State) (negative : Bool) (depth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      InFrame s [pending.value,row,gs,remainder,j,.null,.null,.null] next ∧
      evalBinOp .lt j (.zz 0) = .ok (.bool negative) ∧
      catchReturn (eval depth (if negative then reductionMoveHead else reductionCancel)
        [frame s 8] next) = .ok (result,after) := by
  obtain ⟨j,next,negative,depth,selected,selectorDepth,smaller,bindings,hf,cmp,_,run⟩ :=
    successful_selected fuel pending row gs remainder s after result globals zero success
  exact ⟨j,next,negative,depth,smaller,bindings,hf,cmp,run⟩

end Macaulean.M2.Verification.ReductionDispatch
