import Macaulean.Interpreter.Runtime
namespace Macaulean.M2.Runtime

def Normal (r : Except Signal α) : Prop :=
  ∀ v s, r ≠ .error (.returned v s)

theorem Normal.ok (x : α) : Normal (.ok x) := by intro v s h; cases h

theorem Normal.error (e : Error) : Normal (α := α) (.error (.error e)) := by
  intro v s h; cases h

theorem Normal.bind {r : Except Signal α} {f : α → Except Signal β}
    (h : Normal r) (hf : ∀ x, Normal (f x)) : Normal (r >>= f) := by
  cases r with
  | ok x => exact hf x
  | error e =>
    cases e with
    | error e => exact .error e
    | returned v s => exact False.elim (h v s rfl)

theorem Normal.lift (r : Except Error α) : Normal (liftResult r) := by
  cases r with
  | ok x => exact .ok x
  | error e => exact .error e

theorem Normal.catchReturn (r : Result Value) : Normal (Runtime.catchReturn r) := by
  cases r with
  | ok x => exact .ok x
  | error e => cases e with
    | error e => exact .error e
    | returned v s => exact .ok (v,s)

theorem library_call_normal (fuel : Nat) (name : String) (arg : Value) (s : State) :
    Normal (call fuel (.algebra (.library name)) arg s) := by
  cases fuel with
  | zero => exact .error .fuelExhausted
  | succ fuel =>
    unfold call
    dsimp only
    split
    · apply Normal.bind (Normal.lift _)
      intro values
      exact Normal.catchReturn _
    · exact Normal.error _

theorem builtin_call_normal (fuel : Nat) (primitive : Polynomials.Primitive)
    (arg : Value) (s : State) : Normal (call fuel (.algebra (.builtin primitive)) arg s) := by
  cases fuel with
  | zero => exact .error .fuelExhausted
  | succ fuel =>
    unfold call
    dsimp only
    apply Normal.bind (Normal.lift _)
    intro value
    exact Normal.ok _
end Macaulean.M2.Runtime
