import Macaulean.Verification.Handles.LocalFrame
import Macaulean.Verification.Handles.Intro

/-! Compositional execution rules for private local state and early returns.
Both exit paths carry the final private slots and preserve the caller's cells. -/
namespace Macaulean.M2.Handles
open Lexical Macaulean.M2.Runtime
open Verification.RowProgram (AllocatesOnly)

/-- A completed expression either yields a value or exits the current function. -/
inductive LocalExit (α : Type) where
  | normal (value : α)
  | returned (value : Value)

def LocalExit.result (o : LocalExit α) (s : State) : Except Signal (α × State) :=
  match o with
  | .normal v => .ok (v, s)
  | .returned v => .error (.returned v s)

def LocalExit.post (o : LocalExit α) (vs : List Value)
    (Q : α → List Value → Prop) (R : Value → List Value → Prop) : Prop :=
  match o with
  | .normal v => Q v vs
  | .returned v => R v vs

/-- Completed normal and return outcomes are stable under additional fuel. -/
theorem eval_exit_mono {o : LocalExit Value} {n m : Nat} (h : n ≤ m)
    (he : eval n code fs s = o.result t) : eval m code fs s = o.result t := by
  induction h with
  | refl => exact he
  | step _ ih =>
    rcases (Verification.Fuel.step _).1 code fs s with h | h
    · rw [ih] at h
      cases o <;> cases h
    · rw [← h]; exact ih

/-- Total correctness with separate normal and early-return postconditions. -/
def LocalRuns (p : State) (fs : Frames) (code : Code) (s : State)
    (Q R : Value → List Value → Prop) : Prop :=
  ∃ fuel, ∃ (o : LocalExit Value), ∃ t vs,
    eval fuel code fs s = o.result t ∧ LocalFrame p fs vs t ∧ o.post vs Q R

namespace LocalRuns
variable {p s : State} {fs : Frames} {vs : List Value}
  {a b : Code} {Q R : Value → List Value → Prop}

theorem mono (h : LocalRuns p fs a s Q R)
    (hq : ∀ v vs, Q v vs → Q' v vs) (hr : ∀ v vs, R v vs → R' v vs) :
    LocalRuns p fs a s Q' R' := by
  obtain ⟨n, o, t, ws, he, hf, hp⟩ := h
  refine ⟨n, o, t, ws, he, hf, ?_⟩
  cases o with
  | normal v => exact hq v ws hp
  | returned v => exact hr v ws hp

/-- Existing read-only body proofs also work inside a mutable activation. -/
theorem of_wpV {S : State} (base : Extends S p) (frame : LocalFrame p fs vs s)
    (h : wpV S vs a (fun v => Q v vs)) : LocalRuns p fs a s Q R := by
  have g : Frame S vs fs s := {
    base := base.allocates frame.allocates
    slot := by
      intro i v hv
      have hi := (List.getElem?_eq_some_iff.mp hv).1
      refine ⟨p.heap.cells.length + i, frame.slots i hi, ?_⟩
      obtain ⟨extra, he⟩ := frame.cells
      rw [he, List.append_assoc, List.getElem?_append_right (by omega)]
      simpa [List.getElem?_append_left hi] using hv }
  obtain ⟨n, v, t, he, hq, ht⟩ := runs g a _ s (.rfl' _) h
  exact ⟨n, .normal v, t, vs, he, frame.after_call ht, hq⟩

/-- A return from the first expression skips the second expression. -/
theorem seq (h : LocalRuns p fs a s
    (fun _ ws => ∀ t, LocalFrame p fs ws t → LocalRuns p fs b t Q R) R) :
    LocalRuns p fs (.seq a b) s Q R := by
  obtain ⟨n, o, t, ws, he, hf, hp⟩ := h
  cases o with
  | returned v =>
    exact ⟨n+1, .returned v, t, ws,
      by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
  | normal v =>
    obtain ⟨m, o, u, zs, hb, hg, hq⟩ := hp t hf
    have ha := eval_exit_mono (Nat.le_max_left n m) he
    have hb := eval_exit_mono (Nat.le_max_right n m) hb
    exact ⟨max n m + 1, o, u, zs,
      by simp [eval, ha, LocalExit.result, bind, Except.bind, hb], hg, hq⟩

/-- Returning while evaluating the return operand is already an early exit. -/
theorem returnTerm (h : LocalRuns p fs a s R R) :
    LocalRuns p fs (.returnTerm a) s Q R := by
  obtain ⟨n, o, t, ws, he, hf, hp⟩ := h
  cases o with
  | normal v =>
    exact ⟨n+1, .returned v, t, ws,
      by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
  | returned v =>
    exact ⟨n+1, .returned v, t, ws,
      by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩

/-- Assignment changes a private slot only after its operand finishes normally. -/
theorem set (i : Nat) (h : LocalRuns p fs a s
    (fun v ws => i < ws.length ∧ Q v (ws.set i v)) R) :
    LocalRuns p fs (.set (.slot 0 i) a) s Q R := by
  obtain ⟨n, o, t, ws, he, hf, hp⟩ := h
  cases o with
  | normal v =>
    obtain ⟨hi, hq⟩ := hp
    obtain ⟨u, hw, hg⟩ := hf.write i v hi
    exact ⟨n+1, .normal v, u, ws.set i v,
      by simp [eval, checkWritable, he, LocalExit.result, hw, liftResult,
        Except.mapError, bind, Except.bind, pure, Except.pure], hg, hq⟩
  | returned v =>
    exact ⟨n+1, .returned v, t, ws,
      by simp [eval, checkWritable, he, LocalExit.result, liftResult,
        Except.mapError, bind, Except.bind], hf, hp⟩

end LocalRuns

/-- Local assignment and early return preserve the existing function contract.
Extra local slots begin with `null`, as in the production closure caller. -/
theorem _root_.Macaulean.M2.Fn.Call.Sat.introLocal
    {S : State} {id : Nat} {params : Parameters} {slots : Nat} {body : Code}
    {captured : Frames} {arg : Value} {vs : List Value} {Q : Value → Prop}
    (hf : S.heap.functions[id]? = some (.closure params slots body captured))
    (ha : arguments params arg = .ok vs)
    (h : ∀ t, Extends S t →
      let locals := vs ++ List.replicate (slots - vs.length) .null
      LocalRuns t ((t.allocate locals).1 :: captured) body (t.allocate locals).2
        (fun v _ => Q v) (fun v _ => Q v)) :
    Fn.Call.Sat ⟨⟨S, .closure id⟩, arg⟩ Q := by
  intro t ht
  obtain ⟨n, o, u, ws, he, hg, hq⟩ := h t ht
  cases o with
  | normal v =>
    refine ⟨n+1, v, u, ?_, hq, hg.allocates⟩
    rw [Functions.call_closure n id slots params body captured arg t vs (ht.function hf) ha]
    change catchReturn (eval n body _ _) = _
    dsimp only [State.allocate] at he
    rw [he]; rfl
  | returned v =>
    refine ⟨n+1, v, u, ?_, hq, hg.allocates⟩
    rw [Functions.call_closure n id slots params body captured arg t vs (ht.function hf) ha]
    change catchReturn (eval n body _ _) = _
    dsimp only [State.allocate] at he
    rw [he]; rfl

end Macaulean.M2.Handles
