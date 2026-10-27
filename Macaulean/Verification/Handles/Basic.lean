import Macaulean.Verification.NatContracts.Soundness

/-!
# M2 functions as Lean terms

An `Fn` is an M2 function value together with the runtime state it lives in. A call
`f a` pairs it with an argument, and `f a ⇓ r` says that the production runtime,
started from the function's state or from any state that merely allocated more
cells, returns `r` for some fuel. `f a ↓` says the call terminates.

Arguments and results are written with Lean values: `ToM2` embeds naturals,
integers, rationals, Booleans, lists and raw `Value`s, and a tuple `(a, b)` is the
M2 sequence of its components, as a fixed parameter list expects.
-/
namespace Macaulean.M2
open Lexical
open Verification.RowProgram (AllocatesOnly)

/-- An M2 function value and the runtime state it is interpreted in. -/
structure Fn where
  state : Runtime.State
  value : Value

/-- A call of `fn` on the runtime argument `arg`. -/
structure Fn.Call where
  fn : Fn
  arg : Value

/-- `t` extends `S`: every global of `S` keeps its value, and cells and function
records are only appended. Later worksheet states extend earlier ones unless a
name is redefined; states reached by evaluation extend the states they start from. -/
structure Extends (S t : Runtime.State) : Prop where
  env : ∀ x v, S.env.lookup x = some v → t.env.lookup x = some v
  cells : ∃ fresh, t.heap.cells = S.heap.cells ++ fresh
  functions : ∃ fresh, t.heap.functions = S.heap.functions ++ fresh

namespace Extends
theorem refl (S : Runtime.State) : Extends S S :=
  ⟨fun _ _ h => h, ⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem trans {S t u : Runtime.State} (h : Extends S t) (k : Extends t u) : Extends S u := by
  obtain ⟨xs, hx⟩ := h.cells
  obtain ⟨ys, hy⟩ := k.cells
  obtain ⟨fs, hf⟩ := h.functions
  obtain ⟨gs, hg⟩ := k.functions
  exact ⟨fun x v e => k.env x v (h.env x v e), ⟨xs ++ ys, by rw [hy, hx, List.append_assoc]⟩,
    ⟨fs ++ gs, by rw [hg, hf, List.append_assoc]⟩⟩

theorem of_allocates {S t : Runtime.State} (h : AllocatesOnly S t) : Extends S t :=
  ⟨fun _ _ e => by rw [h.env]; exact e, h.cells, ⟨[], by rw [h.functions]; simp⟩⟩

theorem allocates {S t u : Runtime.State} (h : Extends S t) (k : AllocatesOnly t u) : Extends S u :=
  h.trans (of_allocates k)

theorem cell {S t : Runtime.State} {k : Nat} {v : Value} (h : Extends S t)
    (hk : S.heap.cells[k]? = some v) : t.heap.cells[k]? = some v := by
  obtain ⟨fresh, hf⟩ := h.cells
  rw [hf, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]
  exact hk

theorem function {S t : Runtime.State} {id : Nat} {f : Runtime.Function} (h : Extends S t)
    (hf : S.heap.functions[id]? = some f) : t.heap.functions[id]? = some f := by
  obtain ⟨fresh, e⟩ := h.functions
  rw [e, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hf).1]
  exact hf
private theorem lookup_append_fresh {x : String} {l₁ l₂ : List (String × Value)}
    (h : ∀ p ∈ l₁, p.1 ≠ x) : (l₁ ++ l₂).lookup x = l₂.lookup x := by
  induction l₁ with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨y, w⟩ := p
    have hy : y ≠ x := h (y, w) (by simp)
    have hne : (x == y) = false := beq_false_of_ne fun e => hy e.symm
    simp only [List.cons_append, List.lookup, hne]
    exact ih fun q hq => h q (by simp [hq])

/-- Checkable form: `t`'s globals are new bindings, for names unbound in `S`, in
front of `S`'s; `S`'s cells and function records are prefixes of `t`'s. -/
theorem of_parts {S t : Runtime.State}
    (henv : t.env.drop (t.env.length - S.env.length) = S.env)
    (hnew : ((t.env.take (t.env.length - S.env.length)).all
      fun p => (S.env.lookup p.1).isNone) = true)
    (hcells : t.heap.cells.take S.heap.cells.length = S.heap.cells)
    (hfun : t.heap.functions.take S.heap.functions.length = S.heap.functions) : Extends S t := by
  refine ⟨fun x v e => ?_, ⟨t.heap.cells.drop S.heap.cells.length, ?_⟩,
    ⟨t.heap.functions.drop S.heap.functions.length, ?_⟩⟩
  · rw [← List.take_append_drop (t.env.length - S.env.length) t.env, henv,
      lookup_append_fresh, e]
    intro p hp hx
    have := List.all_eq_true.mp hnew p hp
    rw [hx, e] at this
    simp at this
  · conv => lhs; rw [← List.take_append_drop S.heap.cells.length t.heap.cells]
    rw [hcells]
  · conv => lhs; rw [← List.take_append_drop S.heap.functions.length t.heap.functions]
    rw [hfun]
end Extends

/-- The call terminates with a result satisfying `Q`, started from the function's
state or from any state extending it, and itself only allocates. -/
def Fn.Call.Sat (c : Fn.Call) (Q : Value → Prop) : Prop :=
  ∀ t, Extends c.fn.state t → ∃ fuel r after,
    Runtime.call fuel c.fn.value c.arg t = .ok (r, after) ∧ Q r ∧ AllocatesOnly t after

/-- The call returns `r`. -/
def Fn.Call.Returns (c : Fn.Call) (r : Value) : Prop := c.Sat (· = r)

/-- The call terminates. -/
def Fn.Call.Terminates (c : Fn.Call) : Prop := c.Sat fun _ => True

/-! ## Lean values as M2 values -/

class ToM2 (α : Type) where
  toValue : α → Value

instance : ToM2 Value := ⟨id⟩
instance : ToM2 Nat := ⟨Verification.NatContracts.natV⟩
instance : ToM2 Int := ⟨.zz⟩
instance : ToM2 Rat := ⟨.qq⟩
instance : ToM2 Bool := ⟨.bool⟩
instance [ToM2 α] : ToM2 (List α) := ⟨fun l => .list (l.map ToM2.toValue)⟩

/-- The components of a tuple. -/
class ToM2Seq (α : Type) where
  toSeq : α → List Value

instance (priority := low) [ToM2 α] : ToM2Seq α := ⟨fun a => [ToM2.toValue a]⟩
instance [ToM2 α] [ToM2Seq β] : ToM2Seq (α × β) := ⟨fun p => ToM2.toValue p.1 :: ToM2Seq.toSeq p.2⟩

/-- A call argument: a tuple is an M2 sequence, anything else a single value. -/
class ToM2Arg (α : Type) where
  toArg : α → Value

instance (priority := low) [ToM2 α] : ToM2Arg α := ⟨ToM2.toValue⟩
instance [ToM2 α] [ToM2Seq β] : ToM2Arg (α × β) :=
  ⟨fun p => .sequence (ToM2.toValue p.1 :: ToM2Seq.toSeq p.2)⟩
instance : ToM2Arg Unit := ⟨fun _ => .sequence []⟩

/-- A call argument, coerced from any `ToM2Arg` value. -/
structure Arg where
  value : Value

def Arg.of {α : Type} [ToM2Arg α] (a : α) : Arg := ⟨ToM2Arg.toArg a⟩

instance {α : Type} [ToM2Arg α] (a : α) : CoeDep α a Arg := ⟨Arg.of a⟩

def Fn.call (f : Fn) (a : Arg) : Fn.Call := ⟨f, a.value⟩

instance : CoeFun Fn (fun _ => Arg → Fn.Call) := ⟨Fn.call⟩

@[app_unexpander Fn.call] def unexpandCall : Lean.PrettyPrinter.Unexpander
  | `($_ $f $a) => `($f $a)
  | _ => throw ()

@[app_unexpander Arg.of] def unexpandArg : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `($a)
  | _ => throw ()

/-- `c ⇓ r`: the call returns `r`. -/
notation:50 c:51 " ⇓ " r:51 => Fn.Call.Returns c (ToM2.toValue r)
/-- `c ↓`: the call terminates. -/
notation:50 c:51 " ↓" => Fn.Call.Terminates c

/-! ## Basic laws -/

namespace Fn.Call
variable {c : Fn.Call} {Q Q' : Value → Prop} {r r' : Value}

theorem Sat.mono (h : c.Sat Q) (k : ∀ r, Q r → Q' r) : c.Sat Q' := by
  intro t ht
  obtain ⟨fuel, r, after, hc, hq, ha⟩ := h t ht
  exact ⟨fuel, r, after, hc, k r hq, ha⟩

theorem Sat.terminates (h : c.Sat Q) : c.Terminates := h.mono fun _ _ => trivial

theorem Returns.terminates (h : c.Returns r) : c.Terminates := Sat.terminates h

/-- Run in the function's own state. -/
theorem Sat.call (h : c.Sat Q) :
    ∃ fuel r after, Runtime.call fuel c.fn.value c.arg c.fn.state = .ok (r, after) ∧ Q r := by
  obtain ⟨fuel, r, after, hc, hq, _⟩ := h _ (.refl _)
  exact ⟨fuel, r, after, hc, hq⟩

theorem Terminates.call (h : c.Terminates) :
    ∃ fuel r after, Runtime.call fuel c.fn.value c.arg c.fn.state = .ok (r, after) := by
  obtain ⟨fuel, r, after, hc, _⟩ := Sat.call h
  exact ⟨fuel, r, after, hc⟩

/-- Every successful run in the function's state, at any fuel, satisfies `Q`. -/
theorem Sat.sound (h : c.Sat Q) {fuel : Nat} {v : Value} {after : Runtime.State}
    (hc : Runtime.call fuel c.fn.value c.arg c.fn.state = .ok (v, after)) : Q v := by
  obtain ⟨fuel', r, after', hc', hq⟩ := Sat.call h
  have := Verification.Fuel.call_success_unique fuel fuel' _ _ _ _ _ hc hc'
  rw [(Prod.mk.inj this).1]
  exact hq

theorem Returns.sound (h : c.Returns r) {fuel : Nat} {v : Value} {after : Runtime.State}
    (hc : Runtime.call fuel c.fn.value c.arg c.fn.state = .ok (v, after)) : v = r :=
  Sat.sound h hc

theorem Returns.unique (h : c.Returns r) (h' : c.Returns r') : r = r' := by
  obtain ⟨fuel, v, after, hc, rfl⟩ := Sat.call h
  exact Returns.sound h' hc

/-- A known result discharges any postcondition it satisfies. -/
theorem Sat.of_returns (h : c.Returns r) (hq : Q r) : c.Sat Q :=
  h.mono fun _ e => e ▸ hq

/-- What a terminating call returns satisfies every proved postcondition. -/
theorem Sat.returns (h : c.Sat Q) (hr : c.Returns r) : Q r := by
  obtain ⟨fuel, v, after, hc, hq⟩ := Sat.call h
  rw [← Returns.sound hr hc]
  exact hq

/-- A fact about a function in an earlier worksheet state holds in any later state
that extends it. -/
theorem Sat.transport {S S' : Runtime.State} {v a : Value} (hx : Extends S S')
    (h : (⟨⟨S, v⟩, a⟩ : Fn.Call).Sat Q) : (⟨⟨S', v⟩, a⟩ : Fn.Call).Sat Q :=
  fun t ht => h t (hx.trans ht)

/-- Use a proved result of a call, possibly from an earlier worksheet state. -/
theorem Sat.use {S S' : Runtime.State} {v a : Value} (h : (⟨⟨S, v⟩, a⟩ : Fn.Call).Returns r)
    (hx : Extends S S') (hq : Q r) : (⟨⟨S', v⟩, a⟩ : Fn.Call).Sat Q :=
  Sat.transport hx (Sat.of_returns h hq)

end Fn.Call
end Macaulean.M2
