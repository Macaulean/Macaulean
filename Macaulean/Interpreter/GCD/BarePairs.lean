import Macaulean.Interpreter.GCD.NormalFormPrimitives

namespace Macaulean.M2.GCD.Execution
open Lexical Macaulean.M2.Runtime Univariate
set_option linter.unusedSimpArgs false

def barePairsNext : Code :=
  .apply (globalVar "m2gbBarePairs")
    (.sequence [localVar 0,localVar 1,.binop .add (localVar 2) (.int 1)])

def barePairsBody : Code :=
  .ifElse (.binop .eq (localVar 2) (.unop .length (localVar 0))) (.listLit [])
    (.seq (.set (.slot 0 3) (.apply (globalVar "promote")
      (.sequence [.binop .index (localVar 0) (localVar 2),localVar 1])))
      (.ifElse (.binop .eq (localVar 3) (.int 0)) barePairsNext
        (.binop .concat (.listLit [.listLit [localVar 3,.listLit []]]) barePairsNext)))

theorem bare_pairs_source : Library.lookup "m2gbBarePairs" =
    some (.lambda (.fixed ["F","R","i"]) 4 barePairsBody) := rfl

theorem bare_pairs_end (fuel : Nat) (g ring : Value) (s : State) :
    call (fuel+10) (.algebra (.library "m2gbBarePairs")) (.sequence [.list [g],ring,.zz 1]) s =
      .ok (.list [],(s.allocate [.list [g],ring,.zz 1,.null]).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s bare_pairs_source (by rfl)]
  change catchReturn (eval (fuel+9) barePairsBody
    [(s.allocate [.list [g],ring,.zz 1,.null]).1] (s.allocate [.list [g],ring,.zz 1,.null]).2) = _
  have h0 := allocated_read s [.list [g],ring,.zz 1,.null] 0 (.list [g]) rfl
  have h2 := allocated_read s [.list [g],ring,.zz 1,.null] 2 (.zz 1) rfl
  have heq : evalBinOp .eq (.zz 1) (.zz 1) = .ok (.bool true) := by decide +kernel
  simp only [barePairsBody, localVar, eval, evalMany, h0, h2, length_list,
    List.length_cons, List.length_nil, Nat.reduceAdd, Int.ofNat_one, heq,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

/-- Package a nonzero singleton divisor using the actual source helper. -/
theorem bare_pairs_singleton (fuel id : Nat) (name : String) (s : State)
    (u : Univariate.Term) (us : List Univariate.Term) (hg : Canonical (u :: us))
    (hpromote : s.env.lookup "promote" = some (.algebra (.builtin .promote)))
    (hrecurse : s.env.lookup "m2gbBarePairs" = some (.algebra (.library "m2gbBarePairs"))) :
    ∃ after, Extends s after ∧
      call (fuel+40) (.algebra (.library "m2gbBarePairs"))
        (.sequence [.list [value id name ⟨u :: us⟩],ringValue id name,.zz 0]) s =
        .ok (singletonDivisor id name ⟨u :: us⟩,after) := by
  let vs := [.list [value id name ⟨u :: us⟩],ringValue id name,Value.zz 0,.null]
  have hf := allocated_frame s vs
  obtain ⟨next, hw, hn⟩ := hf.write 3 (value id name ⟨u :: us⟩) (by simp [vs])
  let after := (next.allocate [.list [value id name ⟨u :: us⟩],ringValue id name,.zz 1,.null]).2
  refine ⟨after, hn.extends.trans (allocate_extends next _), ?_⟩
  have h0 := allocated_read s vs 0 (.list [value id name ⟨u :: us⟩]) rfl
  have h1 := allocated_read s vs 1 (ringValue id name) rfl
  have h2 := allocated_read s vs 2 (.zz 0) rfl
  have hn0 := hn.read 0 (.list [value id name ⟨u :: us⟩]) rfl
  have hn1 := hn.read 1 (ringValue id name) rfl
  have hn2 := hn.read 2 (.zz 0) rfl
  have hn3 := hn.read 3 (value id name ⟨u :: us⟩) (by simp [vs])
  change writeRef (.slot 0 3) (value id name ⟨u :: us⟩) [(s.allocate vs).1]
    (s.allocate vs).2 = .ok next at hw
  change readRef (.slot 0 0) [(s.allocate vs).1] next = _ at hn0
  change readRef (.slot 0 1) [(s.allocate vs).1] next = _ at hn1
  change readRef (.slot 0 2) [(s.allocate vs).1] next = _ at hn2
  change readRef (.slot 0 3) [(s.allocate vs).1] next = _ at hn3
  have gp := allocated_global s vs [(s.allocate vs).1] _ _ hpromote
  have gr : readRef (.global "m2gbBarePairs") [(s.allocate vs).1] next =
      .ok (.algebra (.library "m2gbBarePairs")) := by simp [readRef, hn.env, hrecurse]
  have hp := promote_self id name ⟨u :: us⟩ hg
  have hz := eval_eq_zero id name ⟨u :: us⟩ hg
  simp only [List.isEmpty_cons] at hz
  have hend := bare_pairs_end (fuel+24) (value id name ⟨u :: us⟩) (ringValue id name) next
  simp only [Nat.add_assoc, Nat.reduceAdd] at hend
  rw [library_call (fuel+39) _ _ _ _ _ _ s bare_pairs_source (by rfl)]
  change catchReturn (eval (fuel+39) barePairsBody [(s.allocate vs).1] (s.allocate vs).2) = _
  have hconcat : evalBinOp .concat (singletonDivisor id name ⟨u :: us⟩) (.list []) =
      .ok (singletonDivisor id name ⟨u :: us⟩) := rfl
  simp only [barePairsBody, barePairsNext, localVar, globalVar, eval, evalMany,
    checkWritable, h0, h1, h2, hn0, hn1, hn2, hn3, gp, gr, length_list,
    List.length_cons, List.length_nil, Nat.reduceAdd, Int.ofNat_one, zero_ne_one,
    index_zero, builtin_call _ _ _ _ _ hp, hw, hz, zero_add_one, hend,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]
  exact congrArg (fun v => Except.ok (v,after)) (by rfl)

end Macaulean.M2.GCD.Execution
