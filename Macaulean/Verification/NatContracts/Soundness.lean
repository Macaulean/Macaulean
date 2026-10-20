import Macaulean.Verification.NatContracts.Wp

/-!
# Soundness of the natural-number weakest precitions

Proved once for every function body: if a body's verification cition holds,
then for every natural input satisfying the precition the production runtime
call terminates (for some fuel) with a natural number satisfying the
postcition, and every successful call at any fuel returns such a number.
Evaluation only allocates fresh cells; globals and closure records are unchanged.
-/
namespace Macaulean.M2.Verification.NatContracts
open Lexical Macaulean.M2.Runtime
open RowProgram (AllocatesOnly)

/-! ## Fuel monotonicity of successful runs -/

theorem eval_mono {n m : Nat} (h : n ≤ m) (he : eval n code fs s = .ok r) :
    eval m code fs s = .ok r := by
  induction h with
  | refl => exact he
  | step _ ih => exact Fuel.preserves_success ((Fuel.step _).1 code fs s) ih

theorem evalMany_mono {n m : Nat} (h : n ≤ m) (he : evalMany n cs fs s = .ok r) :
    evalMany m cs fs s = .ok r := by
  induction h with
  | refl => exact he
  | step _ ih => exact Fuel.preserves_success ((Fuel.step _).2.1 cs fs s) ih

theorem call_mono {n m : Nat} (h : n ≤ m) (he : call n f a s = .ok r) :
    call m f a s = .ok r := by
  induction h with
  | refl => exact he
  | step _ ih => exact Fuel.preserves_success ((Fuel.step _).2.2 f a s) ih

/-! ## Heap growth -/

theorem _root_.Macaulean.M2.Verification.RowProgram.AllocatesOnly.rfl' (s : State) : AllocatesOnly s s :=
  ⟨rfl, ⟨[], by simp⟩, rfl, rfl⟩

theorem _root_.Macaulean.M2.Verification.RowProgram.AllocatesOnly.cell {k : Nat} (h : AllocatesOnly s t) (hk : s.heap.cells[k]? = some v) :
    t.heap.cells[k]? = some v := by
  obtain ⟨fresh, hf⟩ := h.cells
  rw [hf, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]
  exact hk

theorem _root_.Macaulean.M2.Verification.RowProgram.AllocatesOnly.function (h : AllocatesOnly s t) (id : Nat) :
    t.heap.functions[id]? = s.heap.functions[id]? := by
  rw [h.functions]

/-! ## Arithmetic on natural values, through the production operations -/

section
variable (x y : Nat)
theorem bin_add : evalBinOp .add (natV x) (natV y) = .ok (natV (x + y)) := by
  simp [evalBinOp, natV]
theorem bin_sub (h : y ≤ x) : evalBinOp .sub (natV x) (natV y) = .ok (natV (x - y)) := by
  simp [evalBinOp, natV, Int.ofNat_sub h]
theorem bin_mul : evalBinOp .mul (natV x) (natV y) = .ok (natV (x * y)) := by
  simp [evalBinOp, natV]
theorem bin_quot : evalBinOp .quot (natV x) (natV y) = .ok (natV (x / y)) := by
  simp [evalBinOp, natV]
theorem bin_rem : evalBinOp .rem (natV x) (natV y) = .ok (natV (x % y)) := by
  simp [evalBinOp, natV]
theorem bin_pow : evalBinOp .pow (natV x) (natV y) = .ok (natV (x ^ y)) := by
  simp [evalBinOp, natV]
theorem cmp_eq : evalBinOp .eq (natV x) (natV y) = .ok (.bool (decide (x = y))) := by
  simp [evalBinOp, natV, Value.toRat?, Rat.intCast_inj, Int.natCast_inj]
theorem cmp_ne : evalBinOp .ne (natV x) (natV y) = .ok (.bool (decide (x ≠ y))) := by
  simp [evalBinOp, natV, Value.toRat?, Rat.intCast_inj, Int.natCast_inj]
theorem cmp_lt : evalBinOp .lt (natV x) (natV y) = .ok (.bool (decide (x < y))) := by
  simp [evalBinOp, natV, Value.toRat?, Rat.intCast_lt_intCast]
theorem cmp_le : evalBinOp .le (natV x) (natV y) = .ok (.bool (decide (x ≤ y))) := by
  simp [evalBinOp, natV, Value.toRat?, Rat.intCast_le_intCast]
theorem cmp_gt : evalBinOp .gt (natV x) (natV y) = .ok (.bool (decide (y < x))) := by
  simp [evalBinOp, natV, Value.toRat?, Rat.intCast_lt_intCast]
theorem cmp_ge : evalBinOp .ge (natV x) (natV y) = .ok (.bool (decide (y ≤ x))) := by
  simp [evalBinOp, natV, Value.toRat?, Rat.intCast_le_intCast]
end

/-! ## One evaluation step per supported construct -/

theorem eval_int (n : Nat) (z : Int) (fs : Frames) (s : State) :
    eval (n+1) (.int z) fs s = .ok (.zz z, s) := rfl

theorem eval_read (n : Nat) (ref : Ref) (fs : Frames) (s : State) (v : Value)
    (h : readRef ref fs s = .ok v) : eval (n+1) (.read ref) fs s = .ok (v, s) := by
  simp [eval, h, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem eval_bin (op : BinOp) (x y : Nat) (v : Value)
    (ha : eval n a fs s = .ok (natV x, s₁)) (hb : eval n b fs s₁ = .ok (natV y, s₂))
    (hv : evalBinOp op (natV x) (natV y) = .ok v) :
    eval (n+1) (.binop op a b) fs s = .ok (v, s₂) := by
  cases op <;> simp_all [eval, natV, liftResult, Except.mapError, bind, Except.bind, pure,
    Except.pure]

theorem eval_if_true (hc : eval n c fs s = .ok (.bool true, s₁)) :
    eval (n+1) (.ifElse c yes no) fs s = eval n yes fs s₁ :=
  Functions.branch_true n c yes no fs s s₁ hc

theorem eval_if_false (hc : eval n c fs s = .ok (.bool false, s₁)) :
    eval (n+1) (.ifElse c yes no) fs s = eval n no fs s₁ :=
  Functions.branch_false n c yes no fs s s₁ hc

theorem eval_apply (hf : eval n f fs s = .ok (fv, s₁)) (ha : eval n a fs s₁ = .ok (v, s₂)) :
    eval (n+1) (.apply f a) fs s = call n fv v s₂ := by
  simp [eval, hf, ha, bind, Except.bind]

theorem eval_sequence (h : evalMany n cs fs s = .ok (vs, s₁)) :
    eval (n+1) (.sequence cs) fs s = .ok (.sequence vs, s₁) := by
  simp [eval, h, bind, Except.bind, pure, Except.pure]

theorem evalMany_nil (n : Nat) (fs : Frames) (s : State) :
    evalMany (n+1) [] fs s = .ok ([], s) := rfl

theorem evalMany_cons (ha : eval n a fs s = .ok (v, s₁))
    (hs : evalMany n as fs s₁ = .ok (vs, s₂)) :
    evalMany (n+1) (a :: as) fs s = .ok (v :: vs, s₂) := by
  simp [evalMany, ha, hs, bind, Except.bind, pure, Except.pure]

theorem eval_logic_short (op : LogicOp) (ha : eval n a fs s = .ok (.bool op.shortCircuit, s₁)) :
    eval (n+1) (.logic op a b) fs s = .ok (.bool op.shortCircuit, s₁) :=
  Functions.short_circuit n op a b fs s s₁ ha

theorem eval_logic_long (op : LogicOp) (x y : Bool) (hx : x ≠ op.shortCircuit)
    (ha : eval n a fs s = .ok (.bool x, s₁)) (hb : eval n b fs s₁ = .ok (.bool y, s₂)) :
    eval (n+1) (.logic op a b) fs s = .ok (.bool (logicBool op x y), s₂) := by
  cases op <;> simp_all [eval, callable, evalLogicOp, logicBool, liftResult, Except.mapError,
    bind, Except.bind, pure, Except.pure]

theorem eval_not (ha : eval n a fs s = .ok (.bool x, s₁)) :
    eval (n+1) (.unop .notOp a) fs s = .ok (.bool (!x), s₁) := by
  simp [eval, ha, evalUnOp, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

/-! ## The evaluation invariant of one body -/

/-- The parameter list binds exactly `arity` values. -/
def ParamsArity : Parameters → Nat → Prop
  | .fixed ps, k => ps.length = k
  | .variadic _, k => k = 1

/-- `fs` and `s₀` form a call frame of `fv` on arguments `c.xs`, and every self-call
on arguments of smaller measure already meets the contract. -/
structure Good (c : Ctx) (fv : Value) (fs : Frames) (s₀ : State) : Prop where
  arity : ParamsArity c.params c.contract.arity
  global : s₀.env.lookup c.name = some fv
  slot : ∀ i, i < c.xs.length → ∃ cell, cellAt fs 0 i = some cell ∧
    s₀.heap.cells[cell]? = some (natV (c.xs.getD i 0))
  calls : ∀ ys v, arguments c.params v = .ok (ys.map natV) → ys.length = c.contract.arity →
    c.contract.pre ys → c.contract.measure ys < c.bound → ∀ s, AllocatesOnly s₀ s →
    ∃ fuel r after, call fuel fv v s = .ok (natV r, after) ∧ c.contract.post ys r ∧
      AllocatesOnly s after

def RunsN (fs : Frames) (code : Code) (s : State) (Q : Nat → Prop) : Prop :=
  ∃ fuel n s', eval fuel code fs s = .ok (natV n, s') ∧ Q n ∧ AllocatesOnly s s'
def RunsB (fs : Frames) (code : Code) (s : State) (Q : Bool → Prop) : Prop :=
  ∃ fuel b s', eval fuel code fs s = .ok (.bool b, s') ∧ Q b ∧ AllocatesOnly s s'
def RunsArgs (fs : Frames) (cs : List Code) (s : State) (K : List Nat → Prop) : Prop :=
  ∃ fuel ys s', evalMany fuel cs fs s = .ok (ys.map natV, s') ∧ K ys ∧ AllocatesOnly s s'

/-- A self-call argument: an explicit sequence, or one natural value. -/
def wpCallArg (c : Ctx) (arg : Code) (K : List Nat → Prop) : Prop :=
  match arg with
  | .sequence cs => c.acceptsSequence ∧ wpArgs c cs K
  | _ => wpN c arg fun y => K [y]

theorem wpN_apply (c : Ctx) (f : String) (arg : Code) (Q : Nat → Prop) :
    wpN c (.apply (.read (.global f)) arg) Q = (f = c.name ∧ wpCallArg c arg (c.callPost Q)) := by
  cases arg <;> rfl

section
variable {c : Ctx} {fv : Value} {fs : Frames} {s₀ s : State}

theorem runs_bin {a b : Code} {Q : Nat → Prop} {P : Nat → Prop} (op : BinOp)
    (f : Nat → Nat → Nat) (R : Nat → Nat → Prop)
    (hop : ∀ x y, R x y → evalBinOp op (natV x) (natV y) = .ok (natV (f x y)) ∧ Q (f x y))
    (ha : RunsN fs a s P) (hb : ∀ x s₁, AllocatesOnly s s₁ → P x → RunsN fs b s₁ (R x)) :
    RunsN fs (.binop op a b) s Q := by
  obtain ⟨n₁, x, s₁, ea, px, h₁⟩ := ha
  obtain ⟨n₂, y, s₂, eb, rxy, h₂⟩ := hb x s₁ h₁ px
  obtain ⟨ev, hq⟩ := hop x y rxy
  exact ⟨max n₁ n₂ + 1, f x y, s₂, eval_bin op x y _ (eval_mono (Nat.le_max_left _ _) ea)
    (eval_mono (Nat.le_max_right _ _) eb) ev, hq, h₁.trans h₂⟩

theorem runs_cmp {a b : Code} {Q : Bool → Prop} {P : Nat → Prop} (op : BinOp)
    (f : Nat → Nat → Bool) (hop : ∀ x y, evalBinOp op (natV x) (natV y) = .ok (.bool (f x y)))
    (ha : RunsN fs a s P) (hb : ∀ x s₁, AllocatesOnly s s₁ → P x →
      RunsN fs b s₁ fun y => Q (f x y)) :
    RunsB fs (.binop op a b) s Q := by
  obtain ⟨n₁, x, s₁, ea, px, h₁⟩ := ha
  obtain ⟨n₂, y, s₂, eb, hq, h₂⟩ := hb x s₁ h₁ px
  exact ⟨max n₁ n₂ + 1, f x y, s₂, eval_bin op x y _ (eval_mono (Nat.le_max_left _ _) ea)
    (eval_mono (Nat.le_max_right _ _) eb) (hop x y), hq, h₁.trans h₂⟩

/-- A self-call whose argument evaluates to a value accepted as natural arguments `ys`. -/
theorem runs_call (g : Good c fv fs s₀) {arg : Code} {f : String} {Q : Nat → Prop}
    (hs : AllocatesOnly s₀ s) (hf : f = c.name)
    (ha : ∃ fuel v ys s₁, eval fuel arg fs s = .ok (v, s₁) ∧ c.callPost Q ys ∧
      (ys.length = c.contract.arity → arguments c.params v = .ok (ys.map natV)) ∧
      AllocatesOnly s s₁) :
    RunsN fs (.apply (.read (.global f)) arg) s Q := by
  obtain ⟨n₁, v, ys, s₁, ea, ⟨len, pre, lt, post⟩, args, h₁⟩ := ha
  obtain ⟨n₂, r, after, ec, hpost, h₂⟩ :=
    g.calls ys v (args len) len pre lt s₁ (hs.trans h₁)
  have global : readRef (.global f) fs s = .ok fv := by
    simp [readRef, hf, hs.env, g.global]
  let N := max (max n₁ n₂) 1
  have ef : eval N (.read (.global f)) fs s = .ok (fv, s) :=
    eval_mono (Nat.le_max_right _ _) (eval_read 0 _ fs s fv global)
  have ea' : eval N arg fs s = .ok (v, s₁) :=
    eval_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) ea
  have ec' : call N fv v s₁ = .ok (natV r, after) :=
    call_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) ec
  exact ⟨N+1, r, after, by rw [eval_apply ef ea']; exact ec', post r hpost, h₁.trans h₂⟩

mutual
theorem runsN (g : Good c fv fs s₀) (code : Code) (Q : Nat → Prop) (s : State)
    (hs : AllocatesOnly s₀ s) (h : wpN c code Q) : RunsN fs code s Q := by
  cases code with
  | int z =>
    simp only [wpN] at h
    refine ⟨1, z.toNat, s, ?_, h.2, .rfl' s⟩
    rw [eval_int]; simp [natV, Int.toNat_of_nonneg h.1]
  | read ref =>
    rcases ref with x | ⟨_ | d, i⟩ <;> simp only [wpN] at h
    obtain ⟨hi, hq⟩ := h
    obtain ⟨cell, hc, hv⟩ := g.slot i hi
    exact ⟨1, _, s, eval_read 0 _ fs s _
      (Functions.read_captured_cell fs s 0 i cell _ hc (hs.cell hv)), hq, .rfl' s⟩
  | binop op a b =>
    cases op <;> simp only [wpN] at h
    · exact runs_bin .add (· + ·) (fun x y => Q (x + y)) (fun x y hq => ⟨bin_add x y, hq⟩)
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_bin .sub (· - ·) (fun x y => y ≤ x ∧ Q (x - y))
        (fun x y hq => ⟨bin_sub x y hq.1, hq.2⟩)
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_bin .mul (· * ·) (fun x y => Q (x * y)) (fun x y hq => ⟨bin_mul x y, hq⟩)
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_bin .quot (· / ·) (fun x y => Q (x / y)) (fun x y hq => ⟨bin_quot x y, hq⟩)
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_bin .rem (· % ·) (fun x y => Q (x % y)) (fun x y hq => ⟨bin_rem x y, hq⟩)
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_bin .pow (· ^ ·) (fun x y => Q (x ^ y)) (fun x y hq => ⟨bin_pow x y, hq⟩)
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
  | ifElse cond yes no =>
    simp only [wpN] at h
    obtain ⟨n₁, bv, s₁, ec, hb, h₁⟩ := runsB g cond _ s hs h
    cases bv
    · obtain ⟨n₂, r, s₂, en, hq, h₂⟩ := runsN g no Q s₁ (hs.trans h₁) (by simpa using hb)
      refine ⟨max n₁ n₂ + 1, r, s₂, ?_, hq, h₁.trans h₂⟩
      rw [eval_if_false (eval_mono (Nat.le_max_left _ _) ec)]
      exact eval_mono (Nat.le_max_right _ _) en
    · obtain ⟨n₂, r, s₂, en, hq, h₂⟩ := runsN g yes Q s₁ (hs.trans h₁) (by simpa using hb)
      refine ⟨max n₁ n₂ + 1, r, s₂, ?_, hq, h₁.trans h₂⟩
      rw [eval_if_true (eval_mono (Nat.le_max_left _ _) ec)]
      exact eval_mono (Nat.le_max_right _ _) en
  | apply fn arg =>
    cases fn <;> try (simp only [wpN] at h; done)
    rename_i ref
    rcases ref with f | ⟨d, i⟩
    · rw [wpN_apply] at h
      by_cases hseq : ∃ cs, arg = .sequence cs
      · obtain ⟨cs, rfl⟩ := hseq
        obtain ⟨hf, hfixed, hargs⟩ := h
        obtain ⟨n, ys, s₁, es, hk, h₁⟩ := runsArgs g cs _ s hs hargs
        refine runs_call g hs hf ⟨n+1, _, ys, s₁, eval_sequence es, hk, ?_, h₁⟩
        intro len
        have ga := g.arity
        cases hp : c.params with
        | fixed ps =>
          rw [hp] at ga
          exact Functions.fixed_arguments ps _ (by simpa [ParamsArity] using ga.trans len.symm)
        | variadic _ => simp [Ctx.acceptsSequence, hp] at hfixed
      · have h₂ : wpN c arg fun y => c.callPost Q [y] := by
          cases arg <;> first | exact h.2 | exact absurd ⟨_, rfl⟩ hseq
        obtain ⟨n, y, s₁, ea, hk, h₁⟩ := runsN g arg _ s hs h₂
        refine runs_call g hs h.1 ⟨n, _, [y], s₁, ea, hk, ?_, h₁⟩
        intro len
        have ga := g.arity
        cases hp : c.params with
        | fixed ps =>
          rw [hp] at ga
          have one : ps.length = 1 := by simpa [ParamsArity] using ga.trans len.symm
          simp [arguments, natV, one]
        | variadic _ => rfl
    · cases d <;> cases arg <;> simp only [wpN] at h
  | _ => simp only [wpN] at h
termination_by sizeOf code

theorem runsB (g : Good c fv fs s₀) (code : Code) (Q : Bool → Prop) (s : State)
    (hs : AllocatesOnly s₀ s) (h : wpB c code Q) : RunsB fs code s Q := by
  cases code with
  | binop op a b =>
    cases op <;> simp only [wpB] at h
    · exact runs_cmp .eq (fun x y => decide (x = y)) cmp_eq
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_cmp .ne (fun x y => decide (x ≠ y)) cmp_ne
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_cmp .lt (fun x y => decide (x < y)) cmp_lt
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_cmp .le (fun x y => decide (x ≤ y)) cmp_le
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_cmp .gt (fun x y => decide (y < x)) cmp_gt
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
    · exact runs_cmp .ge (fun x y => decide (y ≤ x)) cmp_ge
        (runsN g a _ s hs h) (fun _ s₁ h₁ hb => runsN g b _ s₁ (hs.trans h₁) hb)
  | logic op a b =>
    simp only [wpB] at h
    obtain ⟨n₁, x, s₁, ea, hx, h₁⟩ := runsB g a _ s hs h
    by_cases hsc : x = op.shortCircuit
    · rw [if_pos hsc] at hx
      subst hsc
      exact ⟨n₁+1, _, s₁, eval_logic_short op ea, hx, h₁⟩
    · rw [if_neg hsc] at hx
      obtain ⟨n₂, y, s₂, eb, hy, h₂⟩ := runsB g b _ s₁ (hs.trans h₁) hx
      exact ⟨max n₁ n₂ + 1, _, s₂, eval_logic_long op x y hsc
        (eval_mono (Nat.le_max_left _ _) ea) (eval_mono (Nat.le_max_right _ _) eb), hy,
        h₁.trans h₂⟩
  | unop op a =>
    cases op <;> simp only [wpB] at h
    obtain ⟨n, x, s₁, ea, hx, h₁⟩ := runsB g a _ s hs h
    exact ⟨n+1, _, s₁, eval_not ea, hx, h₁⟩
  | _ => simp only [wpB] at h
termination_by sizeOf code

theorem runsArgs (g : Good c fv fs s₀) (cs : List Code) (K : List Nat → Prop) (s : State)
    (hs : AllocatesOnly s₀ s) (h : wpArgs c cs K) : RunsArgs fs cs s K := by
  cases cs with
  | nil => exact ⟨1, [], s, evalMany_nil 0 fs s, h, .rfl' s⟩
  | cons a as =>
    simp only [wpArgs] at h
    obtain ⟨n₁, y, s₁, ea, hy, h₁⟩ := runsN g a _ s hs h
    obtain ⟨n₂, ys, s₂, es, hk, h₂⟩ := runsArgs g as _ s₁ (hs.trans h₁) hy
    exact ⟨max n₁ n₂ + 1, y :: ys, s₂, evalMany_cons (eval_mono (Nat.le_max_left _ _) ea)
      (evalMany_mono (Nat.le_max_right _ _) es), hk, h₁.trans h₂⟩
termination_by sizeOf cs
end
end

/-! ## Soundness for a function bound in a runtime state -/

section
variable {s : State} {name : String} {id : Nat} {params : Parameters} {body : Code}
  {captured : Frames} {C : Contract}

/-- Total correctness, by strong induction on the contract's measure. -/
theorem total (hg : s.env.lookup name = some (.closure id))
    (hf : s.heap.functions[id]? = some (.closure params C.arity body captured))
    (har : ParamsArity params C.arity) (hvc : VC name params C body) :
    ∀ m xs, C.measure xs = m → xs.length = C.arity → C.pre xs → ∀ v t,
      arguments params v = .ok (xs.map natV) → AllocatesOnly s t →
      ∃ fuel r after, call fuel (.closure id) v t = .ok (natV r, after) ∧ C.post xs r ∧
        AllocatesOnly t after := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro xs hm hl hp v t hv ht
  have hft : t.heap.functions[id]? = some (.closure params C.arity body captured) := by
    rw [ht.function]; exact hf
  have enter : ∀ fuel, call (fuel+1) (.closure id) v t =
      catchReturn (eval fuel body ((t.allocate (xs.map natV)).1 :: captured)
        (t.allocate (xs.map natV)).2) := by
    intro fuel
    rw [Functions.call_closure fuel id C.arity params body captured v t _ hft hv]
    have : C.arity - (xs.map natV).length = 0 := by simp [hl]
    simp only [this, List.replicate_zero, List.append_nil]
  have g : Good ⟨name, params, C, xs, C.measure xs⟩ (.closure id)
      ((t.allocate (xs.map natV)).1 :: captured) (t.allocate (xs.map natV)).2 := {
    arity := har
    global := by
      change t.env.lookup name = _
      rw [ht.env]; exact hg
    slot := by
      intro i hi
      refine ⟨t.heap.cells.length + i, ?_, ?_⟩
      · simp [State.allocate, cellAt, hi]
      · simp [State.allocate, hi, List.getD_eq_getElem?_getD]
    calls := by
      intro ys w hw hyl hyp hlt t' ht'
      exact ih (C.measure ys) (hm ▸ hlt) ys rfl hyl hyp w t' hw
        (ht.trans ((AllocatesOnly.allocate t _).trans ht')) }
  obtain ⟨fuel, n, s', ev, hq, h'⟩ := runsN g body _ _ (.rfl' _) (hvc xs hp)
  exact ⟨fuel+1, n, s', by rw [enter, ev]; rfl, hq, (AllocatesOnly.allocate t _).trans h'⟩

/-- The verified contract: on natural arguments satisfying `pre`, passed as any value
the parameter list unpacks to them, the call succeeds for some fuel with a natural
result satisfying `post`, and every successful call at any fuel returns such a result. -/
theorem verified (hg : s.env.lookup name = some (.closure id))
    (hf : s.heap.functions[id]? = some (.closure params C.arity body captured))
    (har : ParamsArity params C.arity) (hvc : VC name params C body)
    (xs : List Nat) (hl : xs.length = C.arity) (hp : C.pre xs)
    (arg : Value) (hv : arguments params arg = .ok (xs.map natV)) :
    (∃ fuel r after, call fuel (.closure id) arg s = .ok (natV r, after) ∧ C.post xs r) ∧
    (∀ fuel v after, call fuel (.closure id) arg s = .ok (v, after) →
      ∃ r, v = natV r ∧ C.post xs r) := by
  obtain ⟨fuel, r, after, he, hq, _⟩ := total hg hf har hvc _ xs rfl hl hp _ s hv (.rfl' s)
  refine ⟨⟨fuel, r, after, he, hq⟩, fun fuel' v after' he' => ?_⟩
  have := Fuel.call_success_unique fuel' fuel _ _ s _ _ he' he
  exact ⟨r, (Prod.mk.inj this).1, hq⟩
end

end Macaulean.M2.Verification.NatContracts
