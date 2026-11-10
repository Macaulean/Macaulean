import Macaulean.Verification.Handles.LocalExecution

/-! Weakest preconditions thread private local values through every operand.
A separate return continuation skips the enclosing expression's remaining work. -/
namespace Macaulean.M2.Handles
open Lexical Macaulean.M2.Runtime
open Verification.NatContracts (eval_mono evalMany_mono call_mono logicBool)

mutual
def wpLocal (S : State) (vs : List Value) : Code →
    (Value → List Value → Prop) → (Value → List Value → Prop) → Prop
  | .int z, Q, _ => Q (.zz z) vs
  | .empty, Q, _ => Q .null vs
  | .read (.slot 0 i), Q, _ => ∃ v, vs[i]? = some v ∧ Q v vs
  | .read (.global x), Q, _ => ∃ v, S.env.lookup x = some v ∧ Q v vs
  | .set (.slot 0 i) a, Q, R => wpLocal S vs a (fun v ws => i < ws.length ∧ Q v (ws.set i v)) R
  | .returnTerm a, _, R => wpLocal S vs a R R
  | .seq a b, Q, R => wpLocal S vs a (fun _ ws => wpLocal S ws b Q R) R
  | .unop op a, Q, R => wpLocal S vs a (fun v ws =>
      UnopPure op v ∧ ∃ w, evalUnOp op v = .ok w ∧ Q w ws) R
  | .binop op a b, Q, R => wpLocal S vs a (fun va ws => wpLocal S ws b (fun vb zs =>
      BinopPure op vb ∧ ∃ w, evalBinOp op va vb = .ok w ∧ Q w zs) R) R
  | .logic op a b, Q, R => wpLocal S vs a (fun va ws => boolCase va fun x =>
      if x = op.shortCircuit then Q (.bool x) ws
      else wpLocal S ws b (fun vb zs => boolCase vb fun y => Q (.bool (logicBool op x y)) zs) R) R
  | .ifThen c yes, Q, R => wpLocal S vs c (fun v ws => boolCase v fun b =>
      if b then wpLocal S ws yes Q R else Q .null ws) R
  | .ifElse c yes no, Q, R => wpLocal S vs c (fun v ws => boolCase v fun b =>
      if b then wpLocal S ws yes Q R else wpLocal S ws no Q R) R
  | .listLit cs, Q, R => wpLocalArgs S vs cs (fun values ws => Q (.list values) ws) R
  | .sequence cs, Q, R => wpLocalArgs S vs cs (fun values ws => Q (.sequence values) ws) R
  | .apply f a, Q, R => wpLocal S vs f (fun fv ws => wpLocal S ws a (fun av zs =>
      Fn.Call.Sat ⟨⟨S, fv⟩, av⟩ (fun v => Q v zs)) R) R
  | _, _, _ => False

def wpLocalArgs (S : State) (vs : List Value) : List Code →
    (List Value → List Value → Prop) → (Value → List Value → Prop) → Prop
  | [], Q, _ => Q [] vs
  | a :: as, Q, R => wpLocal S vs a (fun v ws =>
      wpLocalArgs S ws as (fun values zs => Q (v :: values) zs) R) R
end

def LocalRunsArgs (p : State) (fs : Frames) (cs : List Code) (s : State)
    (Q : List Value → List Value → Prop) (R : Value → List Value → Prop) : Prop :=
  ∃ fuel, ∃ (o : LocalExit (List Value)), ∃ t vs,
    evalMany fuel cs fs s = o.result t ∧ LocalFrame p fs vs t ∧ o.post vs Q R

theorem evalMany_exit_mono {o : LocalExit (List Value)} {n m : Nat} (h : n ≤ m)
    (he : evalMany n cs fs s = o.result t) : evalMany m cs fs s = o.result t := by
  induction h with
  | refl => exact he
  | step _ ih =>
    rcases (Verification.Fuel.step _).2.1 cs fs s with h | h
    · rw [ih] at h; cases o <;> cases h
    · rw [← h]; exact ih

mutual
theorem localRuns {S p : State} (base : Extends S p) {fs : Frames}
    {vs : List Value} {s : State} (frame : LocalFrame p fs vs s)
    (code : Code) (Q R : Value → List Value → Prop) (h : wpLocal S vs code Q R) :
    LocalRuns p fs code s Q R := by
  cases code with
  | int z => exact ⟨1, .normal (.zz z), s, vs, rfl, frame, h⟩
  | empty => exact ⟨1, .normal .null, s, vs, rfl, frame, h⟩
  | read ref =>
    rcases ref with x | ⟨_ | d, i⟩ <;> simp only [wpLocal] at h
    · obtain ⟨v, hv, hq⟩ := h
      exact ⟨1, .normal v, s, vs, Verification.NatContracts.eval_read 0 _ fs s v
        (by simp [readRef, frame.env, base.env x v hv]), frame, hq⟩
    · obtain ⟨v, hv, hq⟩ := h
      exact ⟨1, .normal v, s, vs, Verification.NatContracts.eval_read 0 _ fs s v
        (frame.read i v hv), frame, hq⟩
  | set ref a =>
    rcases ref with x | ⟨_ | d, i⟩ <;> simp only [wpLocal] at h
    exact LocalRuns.set i (localRuns base frame a _ R h)
  | returnTerm a => exact LocalRuns.returnTerm (localRuns base frame a R R h)
  | seq a b =>
    apply LocalRuns.seq
    exact (localRuns base frame a _ R h).mono
      (fun _ ws hb t ht => localRuns base ht b Q R hb) (fun _ _ hr => hr)
  | unop op a =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame a _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal v =>
      obtain ⟨hu, w, hw, hq⟩ := hp
      exact ⟨n+1, .normal w, t, ws, eval_unop op he hu hw, hf, hq⟩
  | binop op a b =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame a _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal va =>
      obtain ⟨m, o, u, zs, hb, hg, hq⟩ := localRuns base hf b _ R hp
      have he := eval_exit_mono (Nat.le_max_left n m) he
      have hb := eval_exit_mono (Nat.le_max_right n m) hb
      cases o with
      | returned v =>
        exact ⟨max n m + 1, .returned v, u, zs,
          by simp [eval, he, hb, LocalExit.result, bind, Except.bind], hg, hq⟩
      | normal vb =>
        obtain ⟨hu, w, hw, hq⟩ := hq
        exact ⟨max n m + 1, .normal w, u, zs, eval_binop op he hb hu hw, hg, hq⟩
  | ifThen c yes =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame c _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal v =>
      obtain ⟨b, rfl, hb⟩ := boolCase_iff.mp hp
      cases b
      · exact ⟨n+1, .normal .null, t, ws, eval_ifThen_false he, hf, hb⟩
      · obtain ⟨m, o, u, zs, hy, hg, hq⟩ := localRuns base hf yes Q R hb
        have he := eval_exit_mono (Nat.le_max_left n m) he
        have hy := eval_exit_mono (Nat.le_max_right n m) hy
        exact ⟨max n m + 1, o, u, zs, by rw [eval_ifThen_true he]; exact hy, hg, hq⟩
  | ifElse c yes no =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame c _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal v =>
      obtain ⟨b, rfl, hb⟩ := boolCase_iff.mp hp
      cases b
      · obtain ⟨m, o, u, zs, hn, hg, hq⟩ := localRuns base hf no Q R hb
        have he := eval_exit_mono (Nat.le_max_left n m) he
        have hn := eval_exit_mono (Nat.le_max_right n m) hn
        exact ⟨max n m + 1, o, u, zs,
          by rw [Verification.NatContracts.eval_if_false he]; exact hn, hg, hq⟩
      · obtain ⟨m, o, u, zs, hy, hg, hq⟩ := localRuns base hf yes Q R hb
        have he := eval_exit_mono (Nat.le_max_left n m) he
        have hy := eval_exit_mono (Nat.le_max_right n m) hy
        exact ⟨max n m + 1, o, u, zs,
          by rw [Verification.NatContracts.eval_if_true he]; exact hy, hg, hq⟩
  | logic op a b =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame a _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal v =>
      obtain ⟨x, rfl, hx⟩ := boolCase_iff.mp hp
      by_cases hsc : x = op.shortCircuit
      · rw [if_pos hsc] at hx
        subst hsc
        exact ⟨n+1, .normal _, t, ws, Verification.NatContracts.eval_logic_short op he, hf, hx⟩
      · rw [if_neg hsc] at hx
        obtain ⟨m, o, u, zs, hb, hg, hq⟩ := localRuns base hf b _ R hx
        have he := eval_exit_mono (Nat.le_max_left n m) he
        have hb := eval_exit_mono (Nat.le_max_right n m) hb
        cases o with
        | returned v =>
          exact ⟨max n m + 1, .returned v, u, zs,
            by simp [eval, he, hb, LocalExit.result, hsc, bind, Except.bind], hg, hq⟩
        | normal v =>
          obtain ⟨y, rfl, hy⟩ := boolCase_iff.mp hq
          exact ⟨max n m + 1, .normal _, u, zs,
            Verification.NatContracts.eval_logic_long op x y hsc he hb, hg, hy⟩
  | listLit cs =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRunsArgs base frame cs _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal values => exact ⟨n+1, .normal (.list values), t, ws, eval_listLit he, hf, hp⟩
  | sequence cs =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRunsArgs base frame cs _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal values => exact ⟨n+1, .normal (.sequence values), t, ws,
        Verification.NatContracts.eval_sequence he, hf, hp⟩
  | apply f a =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame f _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [eval, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal fv =>
      obtain ⟨m, o, u, zs, hb, hg, hq⟩ := localRuns base hf a _ R hp
      cases o with
      | returned v =>
        have he := eval_exit_mono (Nat.le_max_left n m) he
        have hb := eval_exit_mono (Nat.le_max_right n m) hb
        exact ⟨max n m + 1, .returned v, u, zs,
          by simp [eval, he, hb, LocalExit.result, bind, Except.bind], hg, hq⟩
      | normal av =>
        obtain ⟨k, v, after, hc, hq, ha⟩ := hq u (base.allocates hg.allocates)
        have he := eval_exit_mono (Nat.le_trans (Nat.le_max_left n m) (Nat.le_max_left (max n m) k)) he
        have hb := eval_exit_mono (Nat.le_trans (Nat.le_max_right n m) (Nat.le_max_left (max n m) k)) hb
        have hc := call_mono (Nat.le_max_right (max n m) k) hc
        exact ⟨max (max n m) k + 1, .normal v, after, zs,
          by rw [Verification.NatContracts.eval_apply he hb]; exact hc, hg.after_call ha, hq⟩
  | _ => simp only [wpLocal] at h
termination_by sizeOf code

theorem localRunsArgs {S p : State} (base : Extends S p) {fs : Frames}
    {vs : List Value} {s : State} (frame : LocalFrame p fs vs s)
    (cs : List Code) (Q : List Value → List Value → Prop) (R : Value → List Value → Prop)
    (h : wpLocalArgs S vs cs Q R) : LocalRunsArgs p fs cs s Q R := by
  cases cs with
  | nil => exact ⟨1, .normal [], s, vs, rfl, frame, h⟩
  | cons a as =>
    obtain ⟨n, o, t, ws, he, hf, hp⟩ := localRuns base frame a _ R h
    cases o with
    | returned v =>
      exact ⟨n+1, .returned v, t, ws,
        by simp [evalMany, he, LocalExit.result, bind, Except.bind], hf, hp⟩
    | normal v =>
      obtain ⟨m, o, u, zs, hb, hg, hq⟩ := localRunsArgs base hf as _ R hp
      have he := eval_exit_mono (Nat.le_max_left n m) he
      have hb := evalMany_exit_mono (Nat.le_max_right n m) hb
      cases o with
      | returned v =>
        exact ⟨max n m + 1, .returned v, u, zs,
          by simp [evalMany, he, hb, LocalExit.result, bind, Except.bind], hg, hq⟩
      | normal values =>
        exact ⟨max n m + 1, .normal (v :: values), u, zs,
          Verification.NatContracts.evalMany_cons he hb, hg, hq⟩
termination_by sizeOf cs
end

/-- Discharge a function call using its local-state weakest precondition. -/
theorem _root_.Macaulean.M2.Fn.Call.Sat.introLocalWp
    {S : State} {id : Nat} {params : Parameters} {slots : Nat} {body : Code}
    {captured : Frames} {arg : Value} {vs : List Value} {Q : Value → Prop}
    (hf : S.heap.functions[id]? = some (.closure params slots body captured))
    (ha : arguments params arg = .ok vs)
    (h : wpLocal S (vs ++ List.replicate (slots - vs.length) .null) body
      (fun v _ => Q v) (fun v _ => Q v)) :
    Fn.Call.Sat ⟨⟨S, .closure id⟩, arg⟩ Q := by
  apply Fn.Call.Sat.introLocal hf ha
  intro t ht
  exact localRuns ht (LocalFrame.allocate t _ captured) body _ _ h

end Macaulean.M2.Handles
