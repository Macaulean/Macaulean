import Macaulean.Verification.Handles.Basic

/-!
# Introduction rules for calls, proved once

`wpV S vs code Q` says that `code`, run as a body of a function whose argument
slots hold `vs` and whose globals are those of `S`, evaluates to a value satisfying
`Q`. Calls inside the body are delegated to `Fn.Call.Sat`, so a call to any
function, including the function itself, is discharged by a theorem about that
function. Constructs that write state, create functions, return early or build
rings have weakest precondition `False`.

`Fn.Call.Sat.intro` is the soundness theorem: it is proved once, for every body,
against the production runtime.
-/
namespace Macaulean.M2.Handles
open Lexical Macaulean.M2.Runtime
open Verification.RowProgram (AllocatesOnly)
open Verification.NatContracts (logicBool eval_mono evalMany_mono call_mono)

def isBasis : Value → Bool
  | .algebra (.basis ..) => true
  | _ => false

/-- `op` neither builds a function nor calls `normalForm` on these operands. -/
def BinopPure (op : BinOp) (vb : Value) : Prop := op ≠ .compose ∧ (op = .rem → isBasis vb = false)

/-- `op` does not build a negated predicate function. -/
def UnopPure (op : UnOp) (v : Value) : Prop := op = .notOp → callable v = false

/-- `v` is a Boolean `b` with `k b`. -/
def boolCase (v : Value) (k : Bool → Prop) : Prop :=
  match v with
  | .bool b => k b
  | _ => False

theorem boolCase_bool (b : Bool) (k : Bool → Prop) : boolCase (.bool b) k = k b := rfl

theorem boolCase_iff {v : Value} {k : Bool → Prop} : boolCase v k ↔ ∃ b, v = .bool b ∧ k b := by
  cases v <;> simp [boolCase]

mutual
def wpV (S : State) (vs : List Value) : Code → (Value → Prop) → Prop
  | .int z, Q => Q (.zz z)
  | .empty, Q => Q .null
  | .read (.slot 0 i), Q => ∃ v, vs[i]? = some v ∧ Q v
  | .read (.global x), Q => ∃ v, S.env.lookup x = some v ∧ Q v
  | .unop op a, Q => wpV S vs a fun v => UnopPure op v ∧ ∃ w, evalUnOp op v = .ok w ∧ Q w
  | .binop op a b, Q => wpV S vs a fun va => wpV S vs b fun vb =>
      BinopPure op vb ∧ ∃ w, evalBinOp op va vb = .ok w ∧ Q w
  | .logic op a b, Q => wpV S vs a fun va => boolCase va fun x =>
      if x = op.shortCircuit then Q (.bool x)
      else wpV S vs b fun vb => boolCase vb fun y => Q (.bool (logicBool op x y))
  | .ifThen cond yes, Q => wpV S vs cond fun v => boolCase v fun b =>
      if b then wpV S vs yes Q else Q .null
  | .ifElse cond yes no, Q => wpV S vs cond fun v => boolCase v fun b =>
      if b then wpV S vs yes Q else wpV S vs no Q
  | .seq a b, Q => wpV S vs a fun _ => wpV S vs b Q
  | .listLit cs, Q => wpArgs S vs cs fun ws => Q (.list ws)
  | .sequence cs, Q => wpArgs S vs cs fun ws => Q (.sequence ws)
  | .apply f a, Q => wpV S vs f fun fv => wpV S vs a fun av => Fn.Call.Sat ⟨⟨S, fv⟩, av⟩ Q
  | _, _ => False

def wpArgs (S : State) (vs : List Value) : List Code → (List Value → Prop) → Prop
  | [], K => K []
  | a :: as, K => wpV S vs a fun v => wpArgs S vs as fun ws => K (v :: ws)
end

/-! ## One evaluation step per construct, for arbitrary values -/

section
variable {n : Nat} {fs : Frames} {s s₁ s₂ : State}

theorem eval_empty : eval (n+1) .empty fs s = .ok (.null, s) := rfl

theorem eval_unop (op : UnOp) {a : Code} {v w : Value}
    (ha : eval n a fs s = .ok (v, s₁)) (hp : UnopPure op v) (hw : evalUnOp op v = .ok w) :
    eval (n+1) (.unop op a) fs s = .ok (w, s₁) := by
  simp only [eval, ha, bind, Except.bind]
  cases op with
  | notOp =>
    have hc := hp rfl
    split <;> simp_all [callable, liftResult, Except.mapError, pure, Except.pure]
  | _ => simp_all [liftResult, Except.mapError, pure, Except.pure]

theorem eval_binop (op : BinOp) {a b : Code} {va vb w : Value}
    (ha : eval n a fs s = .ok (va, s₁)) (hb : eval n b fs s₁ = .ok (vb, s₂))
    (hp : BinopPure op vb) (hw : evalBinOp op va vb = .ok w) :
    eval (n+1) (.binop op a b) fs s = .ok (w, s₂) := by
  obtain ⟨hc, hr⟩ := hp
  simp only [eval, ha, hb, bind, Except.bind]
  split <;> simp_all [isBasis, liftResult, Except.mapError, pure, Except.pure]

theorem eval_ifThen_true {c yes : Code} (hc : eval n c fs s = .ok (.bool true, s₁)) :
    eval (n+1) (.ifThen c yes) fs s = eval n yes fs s₁ := by
  simp [eval, hc, bind, Except.bind]

theorem eval_ifThen_false {c yes : Code} (hc : eval n c fs s = .ok (.bool false, s₁)) :
    eval (n+1) (.ifThen c yes) fs s = .ok (.null, s₁) := by
  simp [eval, hc, bind, Except.bind, pure, Except.pure]

theorem eval_seq {a b : Code} {v : Value} (ha : eval n a fs s = .ok (v, s₁)) :
    eval (n+1) (.seq a b) fs s = eval n b fs s₁ := by
  simp [eval, ha, bind, Except.bind]

theorem eval_listLit {cs : List Code} {ws : List Value} (h : evalMany n cs fs s = .ok (ws, s₁)) :
    eval (n+1) (.listLit cs) fs s = .ok (.list ws, s₁) := by
  simp [eval, h, bind, Except.bind, pure, Except.pure]
end

/-! ## Soundness -/

/-- `fs` is a frame whose slots hold `vs` in `s₀`, and `s₀` extends `S`. -/
structure Frame (S : State) (vs : List Value) (fs : Frames) (s₀ : State) : Prop where
  base : Extends S s₀
  slot : ∀ i v, vs[i]? = some v → ∃ cell, cellAt fs 0 i = some cell ∧ s₀.heap.cells[cell]? = some v

def Runs (fs : Frames) (code : Code) (s : State) (Q : Value → Prop) : Prop :=
  ∃ fuel v s', eval fuel code fs s = .ok (v, s') ∧ Q v ∧ AllocatesOnly s s'
def RunsArgs (fs : Frames) (cs : List Code) (s : State) (K : List Value → Prop) : Prop :=
  ∃ fuel ws s', evalMany fuel cs fs s = .ok (ws, s') ∧ K ws ∧ AllocatesOnly s s'

section
variable {S : State} {vs : List Value} {fs : Frames} {s₀ : State}

/-- Two successive runs, at a common fuel. -/
private theorem both {a b : Code} {s s₁ s₂ : State} {n₁ n₂ : Nat} {va vb : Value}
    (ea : eval n₁ a fs s = .ok (va, s₁)) (eb : eval n₂ b fs s₁ = .ok (vb, s₂)) :
    eval (max n₁ n₂) a fs s = .ok (va, s₁) ∧ eval (max n₁ n₂) b fs s₁ = .ok (vb, s₂) :=
  ⟨eval_mono (Nat.le_max_left _ _) ea, eval_mono (Nat.le_max_right _ _) eb⟩

mutual
theorem runs (g : Frame S vs fs s₀) (code : Code) (Q : Value → Prop) (s : State)
    (hs : AllocatesOnly s₀ s) (h : wpV S vs code Q) : Runs fs code s Q := by
  cases code with
  | int z => exact ⟨1, _, s, rfl, h, .rfl' s⟩
  | empty => exact ⟨1, _, s, rfl, h, .rfl' s⟩
  | read ref =>
    rcases ref with x | ⟨_ | d, i⟩ <;> simp only [wpV] at h
    · obtain ⟨v, hv, hq⟩ := h
      have : readRef (.global x) fs s = .ok v := by
        simp [readRef, hs.env, g.base.env x v hv]
      exact ⟨1, v, s, Verification.NatContracts.eval_read 0 _ fs s v this, hq, .rfl' s⟩
    · obtain ⟨v, hv, hq⟩ := h
      obtain ⟨cell, hc, hcell⟩ := g.slot i v hv
      exact ⟨1, v, s, Verification.NatContracts.eval_read 0 _ fs s v
        (Functions.read_captured_cell fs s 0 i cell v hc (hs.cell hcell)), hq, .rfl' s⟩
  | unop op a =>
    simp only [wpV] at h
    obtain ⟨n, v, s₁, ea, ⟨hp, w, hw, hq⟩, h₁⟩ := runs g a _ s hs h
    exact ⟨n+1, w, s₁, eval_unop op ea hp hw, hq, h₁⟩
  | binop op a b =>
    simp only [wpV] at h
    obtain ⟨n₁, va, s₁, ea, hb, h₁⟩ := runs g a _ s hs h
    obtain ⟨n₂, vb, s₂, eb, ⟨hp, w, hw, hq⟩, h₂⟩ := runs g b _ s₁ (hs.trans h₁) hb
    obtain ⟨ea, eb⟩ := both ea eb
    exact ⟨_, w, s₂, eval_binop op ea eb hp hw, hq, h₁.trans h₂⟩
  | logic op a b =>
    simp only [wpV] at h
    obtain ⟨n₁, va, s₁, ea, hva, h₁⟩ := runs g a _ s hs h
    obtain ⟨x, rfl, hx⟩ := boolCase_iff.mp hva
    by_cases hsc : x = op.shortCircuit
    · rw [if_pos hsc] at hx
      subst hsc
      exact ⟨n₁+1, _, s₁, Verification.NatContracts.eval_logic_short op ea, hx, h₁⟩
    · rw [if_neg hsc] at hx
      obtain ⟨n₂, vb, s₂, eb, hvb, h₂⟩ := runs g b _ s₁ (hs.trans h₁) hx
      obtain ⟨y, rfl, hy⟩ := boolCase_iff.mp hvb
      obtain ⟨ea, eb⟩ := both ea eb
      exact ⟨_, _, s₂, Verification.NatContracts.eval_logic_long op x y hsc ea eb, hy,
        h₁.trans h₂⟩
  | ifThen cond yes =>
    simp only [wpV] at h
    obtain ⟨n₁, v, s₁, ec, hv, h₁⟩ := runs g cond _ s hs h
    obtain ⟨b, rfl, hb⟩ := boolCase_iff.mp hv
    cases b
    · exact ⟨n₁+1, _, s₁, eval_ifThen_false ec, by simpa using hb, h₁⟩
    · obtain ⟨n₂, r, s₂, ey, hq, h₂⟩ := runs g yes Q s₁ (hs.trans h₁) (by simpa using hb)
      obtain ⟨ec, ey⟩ := both ec ey
      exact ⟨_, r, s₂, by rw [eval_ifThen_true ec]; exact ey, hq, h₁.trans h₂⟩
  | ifElse cond yes no =>
    simp only [wpV] at h
    obtain ⟨n₁, v, s₁, ec, hv, h₁⟩ := runs g cond _ s hs h
    obtain ⟨b, rfl, hb⟩ := boolCase_iff.mp hv
    cases b
    · obtain ⟨n₂, r, s₂, en, hq, h₂⟩ := runs g no Q s₁ (hs.trans h₁) (by simpa using hb)
      obtain ⟨ec, en⟩ := both ec en
      exact ⟨_, r, s₂, by rw [Verification.NatContracts.eval_if_false ec]; exact en, hq,
        h₁.trans h₂⟩
    · obtain ⟨n₂, r, s₂, ey, hq, h₂⟩ := runs g yes Q s₁ (hs.trans h₁) (by simpa using hb)
      obtain ⟨ec, ey⟩ := both ec ey
      exact ⟨_, r, s₂, by rw [Verification.NatContracts.eval_if_true ec]; exact ey, hq,
        h₁.trans h₂⟩
  | seq a b =>
    simp only [wpV] at h
    obtain ⟨n₁, va, s₁, ea, hb, h₁⟩ := runs g a _ s hs h
    obtain ⟨n₂, r, s₂, eb, hq, h₂⟩ := runs g b Q s₁ (hs.trans h₁) hb
    obtain ⟨ea, eb⟩ := both ea eb
    exact ⟨_, r, s₂, by rw [eval_seq ea]; exact eb, hq, h₁.trans h₂⟩
  | listLit cs =>
    simp only [wpV] at h
    obtain ⟨n, ws, s₁, es, hq, h₁⟩ := runsArgs g cs _ s hs h
    exact ⟨n+1, _, s₁, eval_listLit es, hq, h₁⟩
  | sequence cs =>
    simp only [wpV] at h
    obtain ⟨n, ws, s₁, es, hq, h₁⟩ := runsArgs g cs _ s hs h
    exact ⟨n+1, _, s₁, Verification.NatContracts.eval_sequence es, hq, h₁⟩
  | apply f a =>
    simp only [wpV] at h
    obtain ⟨n₁, fv, s₁, ef, ha, h₁⟩ := runs g f _ s hs h
    obtain ⟨n₂, av, s₂, ea, hc, h₂⟩ := runs g a _ s₁ (hs.trans h₁) ha
    obtain ⟨n₃, r, after, ec, hq, h₃⟩ :=
      hc s₂ (g.base.allocates (hs.trans (h₁.trans h₂)))
    let N := max (max n₁ n₂) n₃
    have ef' : eval N f fs s = .ok (fv, s₁) :=
      eval_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) ef
    have ea' : eval N a fs s₁ = .ok (av, s₂) :=
      eval_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) ea
    have ec' : call N fv av s₂ = .ok (r, after) := call_mono (Nat.le_max_right _ _) ec
    exact ⟨N+1, r, after, by rw [Verification.NatContracts.eval_apply ef' ea']; exact ec', hq,
      h₁.trans (h₂.trans h₃)⟩
  | _ => simp only [wpV] at h
termination_by sizeOf code

theorem runsArgs (g : Frame S vs fs s₀) (cs : List Code) (K : List Value → Prop) (s : State)
    (hs : AllocatesOnly s₀ s) (h : wpArgs S vs cs K) : RunsArgs fs cs s K := by
  cases cs with
  | nil => exact ⟨1, [], s, Verification.NatContracts.evalMany_nil 0 fs s, h, .rfl' s⟩
  | cons a as =>
    simp only [wpArgs] at h
    obtain ⟨n₁, v, s₁, ea, hv, h₁⟩ := runs g a _ s hs h
    obtain ⟨n₂, ws, s₂, es, hk, h₂⟩ := runsArgs g as _ s₁ (hs.trans h₁) hv
    exact ⟨max n₁ n₂ + 1, v :: ws, s₂, Verification.NatContracts.evalMany_cons
      (eval_mono (Nat.le_max_left _ _) ea) (evalMany_mono (Nat.le_max_right _ _) es), hk,
      h₁.trans h₂⟩
termination_by sizeOf cs
end
end

/-- Soundness: a closure call satisfies `Q` once its body's weakest precondition holds. -/
theorem _root_.Macaulean.M2.Fn.Call.Sat.intro {S : State} {id : Nat} {params : Parameters}
    {slots : Nat} {body : Code} {captured : Frames}
    (hf : S.heap.functions[id]? = some (.closure params slots body captured))
    {arg : Value} {vs : List Value} (ha : arguments params arg = .ok vs) (hl : vs.length = slots)
    {Q : Value → Prop} (h : wpV S vs body Q) : Fn.Call.Sat ⟨⟨S, .closure id⟩, arg⟩ Q := by
  intro t ht
  have hft : t.heap.functions[id]? = some (.closure params slots body captured) :=
    ht.function hf
  have g : Frame S vs ((t.allocate vs).1 :: captured) (t.allocate vs).2 := {
    base := ht.allocates (AllocatesOnly.allocate t vs)
    slot := by
      intro i v hv
      have hi : i < vs.length := (List.getElem?_eq_some_iff.mp hv).1
      refine ⟨t.heap.cells.length + i, ?_, ?_⟩
      · simp [State.allocate, cellAt, hi]
      · show (t.heap.cells ++ vs)[t.heap.cells.length + i]? = some v
        rw [List.getElem?_append_right (by omega)]
        simpa using hv }
  obtain ⟨fuel, r, s', ev, hq, h'⟩ := runs g body Q _ (.rfl' _) h
  refine ⟨fuel+1, r, s', ?_, hq, (AllocatesOnly.allocate t vs).trans h'⟩
  rw [Functions.call_closure fuel id slots params body captured arg t vs hft ha]
  have : slots - vs.length = 0 := by omega
  simp only [this, List.replicate_zero, List.append_nil, ev]
  rfl

end Macaulean.M2.Handles
