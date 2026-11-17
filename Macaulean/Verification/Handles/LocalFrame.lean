import Macaulean.Verification.Handles.Basic

/-! A function's private slots may change without changing its caller's cells.
The frame list is fixed across writes and may include captured outer frames. -/
namespace Macaulean.M2.Handles
open Lexical Macaulean.M2.Runtime
open Verification.RowProgram (AllocatesOnly)

/-- The current activation's slots occupy fresh cells immediately after the
caller's cells. Nested calls may have appended further cells. -/
structure LocalFrame (parent : State) (fs : Frames) (locals : List Value)
    (current : State) : Prop where
  env : current.env = parent.env
  cells : ∃ extra, current.heap.cells = parent.heap.cells ++ locals ++ extra
  functions : current.heap.functions = parent.heap.functions
  nextRing : current.heap.nextRing = parent.heap.nextRing
  slots : ∀ i, i < locals.length → cellAt fs 0 i = some (parent.heap.cells.length + i)

namespace LocalFrame
variable {p s t : State} {fs : Frames} {vs : List Value}

theorem allocates (h : LocalFrame p fs vs s) : AllocatesOnly p s := by
  obtain ⟨extra, he⟩ := h.cells
  exact ⟨h.env, ⟨vs ++ extra, by simpa [List.append_assoc] using he⟩,
    h.functions, h.nextRing⟩

theorem allocate (p : State) (vs : List Value) (captured : Frames) :
    LocalFrame p ((p.allocate vs).1 :: captured) vs (p.allocate vs).2 := by
  refine ⟨rfl, ⟨[], by simp [State.allocate]⟩, rfl, rfl, ?_⟩
  intro i hi
  simp [cellAt, State.allocate, List.getElem?_range hi]

theorem after_call (h : LocalFrame p fs vs s) (ht : AllocatesOnly s t) :
    LocalFrame p fs vs t := by
  obtain ⟨xs, hx⟩ := h.cells
  obtain ⟨ys, hy⟩ := ht.cells
  exact ⟨ht.env.trans h.env, ⟨xs ++ ys, by simp [hy, hx, List.append_assoc]⟩,
    ht.functions.trans h.functions, ht.nextRing.trans h.nextRing, h.slots⟩

theorem read (h : LocalFrame p fs vs s) (i : Nat) (v : Value)
    (hi : vs[i]? = some v) : readRef (.slot 0 i) fs s = .ok v := by
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨extra, he⟩ := h.cells
  have hcell : s.heap.cells[p.heap.cells.length + i]? = some v := by
    rw [he, List.append_assoc, List.getElem?_append_right (by omega)]
    simpa [List.getElem?_append_left hb] using hi
  simp [readRef, h.slots i hb, hcell, pure, Except.pure]

theorem write (h : LocalFrame p fs vs s) (i : Nat) (v : Value)
    (hi : i < vs.length) :
    ∃ after, writeRef (.slot 0 i) v fs s = .ok after ∧
      LocalFrame p fs (vs.set i v) after := by
  obtain ⟨extra, he⟩ := h.cells
  let after := { s with heap := { s.heap with
    cells := s.heap.cells.set (p.heap.cells.length + i) v } }
  have hb : p.heap.cells.length + i < s.heap.cells.length := by
    simp only [he, List.length_append]; omega
  refine ⟨after, ?_, h.env, ⟨extra, ?_⟩, h.functions, h.nextRing, ?_⟩
  · simp [writeRef, checkWritable, h.slots i hi, hb, after]
    rfl
  · dsimp [after]
    rw [he, List.append_assoc, List.set_append_right _ _ (by omega)]
    simp [List.set_append_left i v hi, List.append_assoc]
  · intro j hj
    exact h.slots j (by simpa using hj)

end LocalFrame
end Macaulean.M2.Handles
