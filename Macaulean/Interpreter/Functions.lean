import Macaulean.Interpreter.Session
import Macaulean.Interpreter.Semantics

/-!
# Laws of the lexical runtime

These statements concern the evaluator used by `run` and the worksheet, not just
the retained loop-free reference evaluator. They cover static binding, captured
frames, return propagation, rollback, and preservation of integer semantics.
-/
namespace Macaulean.M2.Functions
open Lexical Macaulean.M2.Runtime

theorem variadic_arguments (x : String) (v : Value) :
    arguments (.variadic x) v = .ok [v] := rfl

theorem fixed_arguments (names : List String) (vs : List Value)
    (h : names.length = vs.length) :
    arguments (.fixed names) (.sequence vs) = .ok vs := by
  simp [arguments, h]

theorem wrong_arity (names : List String) (vs : List Value)
    (h : names.length ≠ vs.length) :
    arguments (.fixed names) (.sequence vs) = .error (.arity names.length vs.length) := by
  simp [arguments, h]

theorem declare_fresh (r : Resolver) (x : String) :
    (r.declare x).1 = .slot 0 r.current.count ∧
    (r.declare x).2.current.count = r.current.count + 1 := ⟨rfl, rfl⟩

theorem declare_visible (r : Resolver) (x : String) :
    (r.declare x).2.lookup x = .slot 0 r.current.count := by
  simp [Resolver.declare, Resolver.lookup]

/-- A nested function's declarations cannot enlarge its parent's lexical scope. -/
theorem lambda_scope (params : Parameters) (body : Term) (r : Resolver) :
    (resolve (.lambda params body) r).2.current = r.current := by
  simp [resolve]

/-- Dynamic callers do not influence a statically global reference. -/
theorem global_ignores_frames (x : String) (fs gs : Frames) (s : State) :
    readRef (.global x) fs s = readRef (.global x) gs s := rfl

theorem read_captured_cell (fs : Frames) (s : State) (d i cell : Nat) (v : Value)
    (hf : cellAt fs d i = some cell) (hv : s.heap.cells[cell]? = some v) :
    readRef (.slot d i) fs s = .ok v := by
  simp [readRef, hf, hv, pure, Except.pure]

theorem allocation_length (s : State) (vs : List Value) :
    (s.allocate vs).2.heap.cells.length = s.heap.cells.length + vs.length := by
  simp [State.allocate]

theorem allocation_globals (s : State) (vs : List Value) :
    (s.allocate vs).2.env = s.env := rfl

/-- A function captures cell numbers, not a snapshot of their values. -/
theorem lambda_capture (fuel slots : Nat) (params : Parameters) (body : Code)
    (fs : Frames) (s : State) :
    eval (fuel + 1) (.lambda params slots body) fs s =
      .ok (s.function (.closure params slots body fs)) := rfl

/-- Only the function's saved frames are installed under its fresh call frame. -/
theorem call_closure (fuel id slots : Nat) (params : Parameters) (body : Code)
    (captured : Frames) (arg : Value) (s : State) (vs : List Value)
    (hf : s.heap.functions[id]? = some (.closure params slots body captured))
    (ha : arguments params arg = .ok vs) :
    call (fuel + 1) (.closure id) arg s =
      let (frame, next) := s.allocate (vs ++ List.replicate (slots - vs.length) .null)
      catchReturn (eval fuel body (frame :: captured) next) := by
  simp [call, hf, ha, liftResult, Except.mapError, bind, Except.bind]

theorem eval_zero (code : Code) (fs : Frames) (s : State) :
    eval 0 code fs s = .error (.error .fuelExhausted) := rfl

theorem call_zero (f a : Value) (s : State) :
    call 0 f a s = .error (.error .fuelExhausted) := rfl

theorem return_value (fuel : Nat) (a : Code) (fs : Frames) (s next : State) (v : Value)
    (h : eval fuel a fs s = .ok (v, next)) :
    eval (fuel + 1) (.returnTerm a) fs s = .error (.returned v next) := by
  simp [eval, h, bind, Except.bind]

theorem return_skips_block (fuel : Nat) (a skipped : Code) (fs : Frames)
    (s next : State) (v : Value)
    (h : eval fuel a fs s = .error (.returned v next)) :
    eval (fuel + 1) (.seq a skipped) fs s = .error (.returned v next) := by
  simp [eval, h, bind, Except.bind]

theorem call_catches_return (v : Value) (s : State) :
    catchReturn (.error (.returned v s)) = .ok (v, s) := rfl

theorem branch_true (fuel : Nat) (c yes no : Code) (fs : Frames) (s next : State)
    (h : eval fuel c fs s = .ok (.bool true, next)) :
    eval (fuel + 1) (.ifElse c yes no) fs s = eval fuel yes fs next := by
  simp [eval, h, bind, Except.bind]

theorem branch_false (fuel : Nat) (c yes no : Code) (fs : Frames) (s next : State)
    (h : eval fuel c fs s = .ok (.bool false, next)) :
    eval (fuel + 1) (.ifElse c yes no) fs s = eval fuel no fs next := by
  simp [eval, h, bind, Except.bind]

theorem short_circuit (fuel : Nat) (op : LogicOp) (a skipped : Code) (fs : Frames)
    (s next : State) (h : eval fuel a fs s = .ok (.bool op.shortCircuit, next)) :
    eval (fuel + 1) (.logic op a skipped) fs s = .ok (.bool op.shortCircuit, next) := by
  simp [eval, h, bind, Except.bind, pure, Except.pure]

/-- Rollback includes captured cells, closure records, and file-local bindings. -/
theorem session_error_state (s : Session) (t : Term) (fuel : Nat) (error : Error)
    (h : s.evaluate t fuel = .error error) :
    (s.step t false fuel).session = { s with nextInput := s.nextInput + 1 } := by
  simp [Session.step, h]

end Macaulean.M2.Functions

namespace Macaulean.M2.IntExpr
open Lexical Macaulean.M2.Runtime

/-- Resolved form of the existing mathematical integer-expression language. -/
def code : IntExpr → Code
  | .lit n => .int n
  | .neg a => .unop .neg a.code
  | .add a b => .binop .add a.code b.code
  | .sub a b => .binop .sub a.code b.code
  | .mul a b => .binop .mul a.code b.code
  | .quot a b => .binop .quot a.code b.code
  | .rem a b => .binop .rem a.code b.code
  | .pow a n => .binop .pow a.code (.int n)

def depth : IntExpr → Nat
  | .lit _ => 0
  | .neg a | .pow a _ => a.depth + 1
  | .add a b | .sub a b | .mul a b | .quot a b | .rem a b => max a.depth b.depth + 1

theorem resolve_toTerm (t : IntExpr) (r : Resolver) :
    resolve t.toTerm r = (t.code, r) := by
  induction t <;> simp_all [toTerm, code, resolve]

/-- Sufficient depth gives the same integer and preserves the complete runtime store. -/
theorem runtime_eval (t : IntExpr) (fuel : Nat) (fs : Frames) (s : State)
    (h : t.depth < fuel) :
    eval fuel t.code fs s = .ok (.zz t.denote, s) := by
  induction t generalizing fuel with
  | lit n =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k => rfl
  | neg a ih =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      simp [code, eval, ih k ha, denote, evalUnOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
  | add a b ia ib =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      have hb : b.depth < k := by simp [depth] at h; omega
      simp [code, eval, ia k ha, ib k hb, denote, evalBinOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
  | sub a b ia ib =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      have hb : b.depth < k := by simp [depth] at h; omega
      simp [code, eval, ia k ha, ib k hb, denote, evalBinOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
  | mul a b ia ib =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      have hb : b.depth < k := by simp [depth] at h; omega
      simp [code, eval, ia k ha, ib k hb, denote, evalBinOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
  | quot a b ia ib =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      have hb : b.depth < k := by simp [depth] at h; omega
      simp [code, eval, ia k ha, ib k hb, denote, evalBinOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
  | rem a b ia ib =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      have hb : b.depth < k := by simp [depth] at h; omega
      simp [code, eval, ia k ha, ib k hb, denote, evalBinOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
  | pow a n ih =>
    cases fuel with
    | zero => simp [depth] at h
    | succ k =>
      have ha : a.depth < k := by simp [depth] at h; omega
      have hk : 0 < k := by omega
      have hn : eval k (.int n) fs s = .ok (.zz n, s) := by
        cases k with
        | zero => omega
        | succ j => rfl
      simp [code, eval, ih k ha, hn, denote, evalBinOp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]

/-- The source runtime's resolution/allocation adapter also preserves arithmetic. -/
theorem runtime_evaluate (t : IntExpr) (fuel : Nat) (s : State) (h : t.depth < fuel) :
    Runtime.evaluate t.toTerm s (fuel := fuel) =
      .ok ⟨.zz t.denote, s, {}, [], []⟩ := by
  simp [Runtime.evaluate, Lexical.prepare, resolve_toTerm, State.allocate,
    runtime_eval t fuel [[]] s h, finish, bind, Except.bind, pure, Except.pure]

end Macaulean.M2.IntExpr
