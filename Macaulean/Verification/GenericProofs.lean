import Macaulean.Verification.Contracts
import Macaulean.Interpreter.Functions

/-!
# Generic source-level proof examples

The identity theorem quantifies over every argument and runtime state. It proves
both a sufficient evaluation budget and the selected Stage 1 contract. It is not
a computation on a sample input, and does not grant intent approval.
-/
namespace Macaulean.M2.Verification.GenericProofs
open Lean Lexical Macaulean.M2.Runtime Contracts Views

def identityBody : Code := .read (.slot 0 0)

theorem read_new_argument (s : State) (v : Value) (captured : Frames) :
    readRef (.slot 0 0) ((s.allocate [v]).1 :: captured) (s.allocate [v]).2 = .ok v := by
  simp [readRef, cellAt, State.allocate, bind, pure, Except.pure]

theorem identity_call (s : State) (id : Nat) (name : String) (captured : Frames)
    (h : s.heap.functions[id]? = some (.closure (.variadic name) 1 identityBody captured))
    (arg : Value) (fuel : Nat) :
    Runtime.call (fuel+2) (.closure id) arg s = .ok (arg, (s.allocate [arg]).2) := by
  rw [Functions.call_closure (fuel+1) id 1 (.variadic name) identityBody captured arg s [arg] h rfl]
  simp only [List.length_cons, List.length_nil, Nat.sub_self, List.replicate_zero, List.append_nil]
  simp [identityBody, Runtime.eval, read_new_argument, Runtime.liftResult,
    Except.mapError, bind, Except.bind, pure, Except.pure, Runtime.catchReturn]

theorem identity_contract (s : State) (id : Nat) (name : String) (captured : Frames)
    (h : s.heap.functions[id]? = some (.closure (.variadic name) 1 identityBody captured)) :
    Contracts.Statement .polynomialIdentity (.closure id) s := by
  intro arg domain fuel result after execution
  obtain ⟨r,p,hp⟩ := domain
  cases fuel with
  | zero => simp [Runtime.call] at execution
  | succ fuel =>
    cases fuel with
    | zero =>
      rw [Functions.call_closure 0 id 1 (.variadic name) identityBody captured arg s [arg] h rfl] at execution
      simp [Runtime.eval, Runtime.catchReturn] at execution
    | succ fuel =>
      rw [identity_call s id name captured h arg fuel] at execution
      cases execution
      exact ⟨r,p,p,hp,hp,equivalent_refl p⟩

/-- The parser/resolver is the actual M2 front end, not a separately typed model. -/
theorem identity_source :
    (Lexical.prepare (.lambda (.variadic "p") (.var "p"))).1 =
      .lambda (.variadic "p") 1 identityBody := rfl

end Macaulean.M2.Verification.GenericProofs
