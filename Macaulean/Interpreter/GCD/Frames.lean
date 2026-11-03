import Macaulean.Interpreter.Runtime

/-! Preservation of caller cells across the fresh frames used by GCD helpers. -/
namespace Macaulean.M2.GCD.Execution
open Lexical Macaulean.M2.Runtime

/-- A helper may append private cells, but leaves existing cells and globals intact. -/
structure Extends (before after : State) : Prop where
  env : after.env = before.env
  cells : ∃ extra, after.heap.cells = before.heap.cells ++ extra

theorem Extends.refl (s : State) : Extends s s :=
  ⟨rfl, ⟨[], by simp⟩⟩

theorem Extends.trans {a b c : State} (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := by
  obtain ⟨xs, hx⟩ := hab.cells
  obtain ⟨ys, hy⟩ := hbc.cells
  exact ⟨hbc.env.trans hab.env, ⟨xs ++ ys, by simp [hy, hx, List.append_assoc]⟩⟩

theorem allocate_extends (s : State) (vs : List Value) :
    Extends s (s.allocate vs).2 :=
  ⟨rfl, ⟨vs, rfl⟩⟩

theorem Extends.read_cell {s t : State} (h : Extends s t)
    (i : Nat) (v : Value) (hv : s.heap.cells[i]? = some v) :
    t.heap.cells[i]? = some v := by
  obtain ⟨extra, he⟩ := h.cells
  have hi := (List.getElem?_eq_some_iff.mp hv).1
  rw [he, List.getElem?_append_left hi]
  exact hv

theorem Extends.read_ref {s t : State} (h : Extends s t)
    (ref : Ref) (frames : Frames) (v : Value)
    (hv : readRef ref frames s = .ok v) :
    readRef ref frames t = .ok v := by
  cases ref with
  | global name => simpa only [readRef, h.env] using hv
  | slot d i =>
    simp only [readRef] at hv ⊢
    cases hc : cellAt frames d i with
    | none => simp [hc] at hv
    | some cell =>
      cases hs : s.heap.cells[cell]? with
      | none => simp [hc, hs] at hv
      | some w =>
        have ht := h.read_cell cell w hs
        simpa [hc, hs, ht] using hv

/-- Writes to a helper's private cells preserve the caller's state prefix. -/
theorem Extends.set_private {s t : State} (h : Extends s t)
    (i : Nat) (v : Value) (hi : s.heap.cells.length ≤ i) :
    Extends s { t with heap := { t.heap with cells := t.heap.cells.set i v } } := by
  obtain ⟨extra, he⟩ := h.cells
  refine ⟨h.env, ⟨extra.set (i - s.heap.cells.length) v, ?_⟩⟩
  simp only [he, List.set_append_right i v hi]

theorem Extends.write_private {s t : State} (h : Extends s t)
    (frames : Frames) (depth index cell : Nat) (v : Value)
    (hc : cellAt frames depth index = some cell)
    (hlower : s.heap.cells.length ≤ cell) (hupper : cell < t.heap.cells.length) :
    ∃ after, writeRef (.slot depth index) v frames t = .ok after ∧ Extends s after := by
  refine ⟨{ t with heap := { t.heap with cells := t.heap.cells.set cell v } }, ?_,
    h.set_private cell v hlower⟩
  simp [writeRef, checkWritable, hc, hupper]
  rfl

/-- The current helper's locals sit between the caller's cells and any frames
allocated by nested calls. -/
structure InFrame (parent : State) (locals : List Value) (current : State) : Prop where
  env : current.env = parent.env
  cells : ∃ extra, current.heap.cells = parent.heap.cells ++ locals ++ extra

def frame (parent : State) (n : Nat) : List Nat :=
  (List.range n).map (parent.heap.cells.length + ·)

theorem allocated_frame (s : State) (vs : List Value) :
    InFrame s vs (s.allocate vs).2 :=
  ⟨rfl, ⟨[], by simp [State.allocate]⟩⟩

theorem InFrame.extends {p s : State} {vs : List Value} (h : InFrame p vs s) :
    Extends p s := by
  obtain ⟨extra, he⟩ := h.cells
  exact ⟨h.env, ⟨vs ++ extra, by simpa [List.append_assoc] using he⟩⟩

theorem InFrame.after_call {p s t : State} {vs : List Value}
    (h : InFrame p vs s) (ht : Extends s t) : InFrame p vs t := by
  obtain ⟨xs, hx⟩ := h.cells
  obtain ⟨ys, hy⟩ := ht.cells
  exact ⟨ht.env.trans h.env, ⟨xs ++ ys, by simp [hy, hx, List.append_assoc]⟩⟩

theorem InFrame.read {p s : State} {vs : List Value} (h : InFrame p vs s)
    (i : Nat) (v : Value) (hi : vs[i]? = some v) :
    readRef (.slot 0 i) [frame p vs.length] s = .ok v := by
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨extra, he⟩ := h.cells
  have hcell : s.heap.cells[p.heap.cells.length + i]? = some v := by
    rw [he, List.append_assoc, List.getElem?_append_right (by omega)]
    simpa [List.getElem?_append_left hb] using hi
  simp [readRef, cellAt, frame, List.getElem?_range hb, hcell,
    bind, pure, Except.pure]

theorem InFrame.write {p s : State} {vs : List Value} (h : InFrame p vs s)
    (i : Nat) (v : Value) (hi : i < vs.length) :
    ∃ after, writeRef (.slot 0 i) v [frame p vs.length] s = .ok after ∧
      InFrame p (vs.set i v) after := by
  obtain ⟨extra, he⟩ := h.cells
  let after := { s with heap := { s.heap with
    cells := s.heap.cells.set (p.heap.cells.length + i) v } }
  have hc : cellAt [frame p vs.length] 0 i = some (p.heap.cells.length + i) := by
    simp [cellAt, frame, List.getElem?_range hi]
  have hb : p.heap.cells.length + i < s.heap.cells.length := by
    simp only [he, List.length_append]
    omega
  refine ⟨after, ?_, h.env, extra, ?_⟩
  · simp [writeRef, checkWritable, hc, hb, after]
    rfl
  · dsimp [after]
    rw [he, List.append_assoc, List.set_append_right _ _ (by omega)]
    simp [List.set_append_left i v hi, List.append_assoc]

theorem InFrame.write_result {p s after : State} {vs : List Value}
    (h : InFrame p vs s) (i : Nat) (v : Value) (hi : i < vs.length)
    (hw : writeRef (.slot 0 i) v [frame p vs.length] s = .ok after) :
    InFrame p (vs.set i v) after := by
  obtain ⟨t, ht, hf⟩ := h.write i v hi
  rw [hw] at ht
  cases Except.ok.inj ht
  exact hf

end Macaulean.M2.GCD.Execution
