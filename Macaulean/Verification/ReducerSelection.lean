import Macaulean.Verification.CallNormal
import Macaulean.Verification.ReductionEffects
import Macaulean.Verification.ReductionTypes

/-! The ordered source selector, separated from representation invariants. -/
namespace Macaulean.M2.Verification.ReducerSelection
open Lexical Macaulean.M2.Runtime GCD.Execution Views ProofJobs.RuntimeReduction

/-- Exactly the pure primitive calls in one selector condition, in source order. -/
def test (pending divisor : Views.Polynomial r) : Except Error Value := do
  let leadingDivisor ← Polynomials.callPrimitive .leadMonomial divisor.value
  let leadingPending ← Polynomials.callPrimitive .leadMonomial pending.value
  Polynomials.callPrimitive .monomialDivides (.sequence [leadingDivisor,leadingPending])

def condition : Code :=
  .apply (globalVar "m2MonomialDivides") (.sequence [
    .apply (globalVar "leadMonomial")
      (.binop .index (.binop .index (localVar 1) (localVar 2)) (.int 0)),
    .apply (globalVar "leadMonomial") (localVar 0)])

private theorem primitive_result (fuel : Nat) (primitive : Polynomials.Primitive)
    (arg : Value) (s : State) :
    call (fuel+1) (.algebra (.builtin primitive)) arg s =
      (show Except Signal (Value × State) from do
        let v ← liftResult (Polynomials.callPrimitive primitive arg)
        pure (v,s)) := rfl

/-- A single ordered-selector condition is primitive-only and leaves the state
unchanged, including when a primitive reports an error. -/
theorem condition_execute (fuel : Nat) (pending divisor : Views.Polynomial r)
    (row gs j : Value) (s : State) (fs : Frames)
    (h0 : readRef (.slot 0 0) fs s = .ok pending.value)
    (h1 : readRef (.slot 0 1) fs s = .ok gs)
    (h2 : readRef (.slot 0 2) fs s = .ok j)
    (index : evalBinOp .index gs j = .ok (.list [divisor.value,row]))
    (globals : PreludeBindings s) :
    eval (fuel+10) condition fs s =
      (show Except Signal (Value × State) from do
        let v ← liftResult (test pending divisor)
        pure (v,s)) := by
  have gm : readRef (.global "leadMonomial") fs s =
      .ok (.algebra (.builtin .leadMonomial)) := by
    simp only [readRef, globals "leadMonomial" (by decide)]
    rfl
  have gd : readRef (.global "m2MonomialDivides") fs s =
      .ok (.algebra (.builtin .monomialDivides)) := by
    simp only [readRef, globals "m2MonomialDivides" (by decide)]
    rfl
  simp only [condition, localVar, globalVar, eval, evalMany, h1, h2, gm, gd,
    index, index_zero, primitive_result, test, liftResult, Except.mapError,
    bind, Except.bind, pure, Except.pure]
  cases Polynomials.callPrimitive .leadMonomial divisor.value <;>
    simp only [gm, h0, primitive_result, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  case ok v =>
    cases Polynomials.callPrimitive .leadMonomial pending.value <;> simp only []

/-- Exact one-step selector dispatch at an in-range natural index. -/
theorem step (fuel : Nat) (pending : Views.Polynomial r)
    (gs : List (RepresentedReducer r n)) (j : Nat) (g : RepresentedReducer r n)
    (atIndex : gs[j]? = some g) (s : State) (globals : PreludeBindings s) :
    call (fuel+14) (.algebra (.library "m2gbReducer"))
      (.sequence [pending.value,.list (gs.map RepresentedReducer.value),.zz j]) s =
    catchReturn (show Except Signal (Value × State) from do
      let allocated := (s.allocate [pending.value,.list (gs.map RepresentedReducer.value),.zz j]).2
      let v ← liftResult (test pending g.polynomial)
      match v with
      | .bool true => pure (.zz j,allocated)
      | .bool false => (call (fuel+10) (.algebra (.library "m2gbReducer"))
          (.sequence [pending.value,.list (gs.map RepresentedReducer.value),.zz (j+1)])
          allocated)
      | _ => .error (.error (.conditionNotBoolean v.className))) := by
  let values := gs.map RepresentedReducer.value
  let vs := [pending.value,Value.list values,Value.zz j]
  have h0 := allocated_read s vs 0 pending.value rfl
  have h1 := allocated_read s vs 1 (.list values) rfl
  have h2 := allocated_read s vs 2 (.zz j) rfl
  have hg : readRef (.global "m2gbReducer") [(s.allocate vs).1] (s.allocate vs).2 =
      .ok (.algebra (.library "m2gbReducer")) := by
    have binding : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer")) :=
      globals "m2gbReducer" (by decide)
    exact allocated_global s vs _ _ _ binding
  have bound : j < values.length := by
    simpa [values] using (List.getElem?_eq_some_iff.mp atIndex).1
  have index : evalBinOp .index (.list values) (.zz j) = .ok g.value := by
    have positive : ¬ (j : Int) < 0 := by omega
    simp [evalBinOp, indexValue, normalizedIndex, positive, bound]
    have hv : values[j]? = some g.value := by simp [values, atIndex]
    rw [(List.getElem?_eq_some_iff.mp hv).2]
    rfl
  have stop : evalBinOp .eq (.zz j) (.zz values.length) = .ok (.bool false) := by
    simp [evalBinOp, Value.toRat?, Rat.intCast_inj, Int.natCast_inj, Nat.ne_of_lt bound]
  have conditionRun := condition_execute (fuel+1) pending g.polynomial g.coefficients.value
    (.list values) (.zz j) (s.allocate vs).2 [(s.allocate vs).1] h0 h1 h2 index
      (globals.allocate vs)
  rw [library_call (fuel+13) _ _ _ _ _ _ s reducer_source (by rfl)]
  change catchReturn (eval (fuel+13) reducerBody [(s.allocate vs).1] (s.allocate vs).2) = _
  have outer : eval (fuel+12) (.binop .eq (localVar 2) (.unop .length (localVar 1)))
      [(s.allocate vs).1] (s.allocate vs).2 = .ok (.bool false,(s.allocate vs).2) := by
    simp only [eval, localVar, h1, h2, length_list, stop, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  change catchReturn (eval (fuel+13) (.ifElse _ _ (.ifElse condition _ _)) _ _) = _
  rw [eval]
  simp only [outer, bind, Except.bind]
  rw [eval]
  simp only [conditionRun, bind, Except.bind]
  cases test pending g.polynomial with
  | error e => rfl
  | ok v =>
    cases v <;> try rfl
    case bool b =>
      cases b <;> simp only [localVar, globalVar, eval, evalMany, h0, h1, h2, hg,
        liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
      all_goals rfl

/-- A negative result certifies that every remaining candidate was actually
checked and rejected. The proof follows source recursion by the suffix length;
it does not assume termination of the outer reduction algorithm. -/
theorem negative (pending : Views.Polynomial r) (gs : List (RepresentedReducer r n))
    (j : Nat) (bound : j ≤ gs.length) (s after : State) (fuel : Nat) (result : Value)
    (globals : PreludeBindings s)
    (run : call fuel (.algebra (.library "m2gbReducer"))
      (.sequence [pending.value,.list (gs.map RepresentedReducer.value),.zz j]) s = .ok (result,after))
    (less : evalBinOp .lt result (.zz 0) = .ok (.bool true)) :
    ∀ k, j ≤ k → ∀ g, gs[k]? = some g → test pending g.polynomial = .ok (.bool false) := by
  induction remaining : gs.length-j using Nat.strongRecOn generalizing j s after fuel result with
  | ind remaining ih =>
    by_cases last : j = gs.length
    · intro k lower g atIndex
      have upper := (List.getElem?_eq_some_iff.mp atIndex).1
      omega
    · have within : j < gs.length := by omega
      let g := gs[j]
      have atIndex : gs[j]? = some g := by simp [g]
      have padded := Fuel.preserves_success (Fuel.call_mono fuel 14 _ _ s) run
      rw [step fuel pending gs j g atIndex s globals] at padded
      cases checked : test pending g.polynomial with
      | error e =>
        simp only [checked, liftResult, Except.mapError, bind, Except.bind, catchReturn] at padded
        cases padded
      | ok v =>
        simp only [checked, liftResult, Except.mapError, bind, Except.bind] at padded
        cases v <;> try (simp only [catchReturn] at padded; contradiction)
        case bool b =>
          cases b
          · rw [(library_call_normal _ _ _ _).catchReturn_eq] at padded
            have rest := ih (gs.length-(j+1)) (by omega) (j+1) (by omega)
              (s.allocate [pending.value,.list (gs.map RepresentedReducer.value),.zz j]).2
              after (fuel+10) result (globals.allocate _) padded less rfl
            intro k lower candidate candidateIndex
            by_cases same : k = j
            · subst k
              rw [atIndex] at candidateIndex
              cases Option.some.inj candidateIndex
              exact checked
            · exact rest k (by omega) candidate candidateIndex
          · have valueEq : Value.zz j = result := congrArg Prod.fst (Except.ok.inj padded)
            rw [← valueEq] at less
            simp only [evalBinOp, Value.toRat?, Except.ok.injEq, Value.bool.injEq,
              decide_eq_true_eq] at less
            have nonnegative : ¬ ((j : Int) : Rat) < ((0 : Int) : Rat) := by
              rw [Rat.intCast_lt_intCast]
              omega
            exact False.elim (nonnegative less)

end Macaulean.M2.Verification.ReducerSelection
