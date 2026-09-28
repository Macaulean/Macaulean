import Macaulean.Verification.Contracts
import Macaulean.Interpreter.Functions

/-!
A generic contract proof about the actual lexical evaluator. This is not a
certificate for one test value. The argument and initial heap are arbitrary;
only the resolved body and its location in that heap are specified.
-/
namespace Macaulean.M2.Verification.ProofJobs.Identity
open Macaulean.M2.Runtime Lexical

/-- The fresh argument slot reads the supplied argument, independently of the
caller's heap size, globals, other closures and the saved enclosing frames. -/
theorem read_fresh_argument (s : State) (arg : Value) (captured : Frames) :
    readRef (.slot 0 0) ((s.allocate [arg]).1 :: captured) (s.allocate [arg]).2 = .ok arg := by
  simp [State.allocate, readRef, cellAt, bind, pure, Except.pure]

/-- Two levels suffice for calling this body. Fresh allocation is made explicit;
this is not a claim that function application preserves the whole heap. -/
theorem call_identity (s : State) (id : Nat) (name : String) (captured : Frames)
    (arg : Value) (fuel : Nat)
    (h : s.heap.functions[id]? =
      some (.closure (.variadic name) 1 (.read (.slot 0 0)) captured)) :
    Runtime.call (fuel + 2) (.closure id) arg s = .ok (arg,(s.allocate [arg]).2) := by
  rw [Functions.call_closure (fuel + 1) id 1 (.variadic name)
    (.read (.slot 0 0)) captured arg s [arg] h rfl]
  simp [Runtime.eval, read_fresh_argument, Runtime.catchReturn,
    Runtime.liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Every successful call returns precisely its argument; small budgets cannot
create a spurious successful result. -/
theorem successful_value (s : State) (id : Nat) (name : String)
    (captured : Frames) (arg result : Value) (after : State) (fuel : Nat)
    (h : s.heap.functions[id]? =
      some (.closure (.variadic name) 1 (.read (.slot 0 0)) captured))
    (he : Runtime.call fuel (.closure id) arg s = .ok (result,after)) : result = arg := by
  cases fuel with
  | zero => cases he
  | succ k =>
    cases k with
    | zero =>
      rw [Functions.call_closure 0 id 1 (.variadic name)
        (.read (.slot 0 0)) captured arg s [arg] h rfl] at he
      simp [Runtime.eval, Runtime.catchReturn] at he
    | succ k =>
      have hc := call_identity s id name captured arg k h
      rw [hc] at he
      exact (congrArg Prod.fst (Except.ok.inj he)).symm

/-- The exact Stage 1 polynomial-identity contract, for all admissible arguments
and all successful evaluations in the specified state. -/
theorem contract (s : State) (id : Nat) (name : String) (captured : Frames)
    (h : s.heap.functions[id]? =
      some (.closure (.variadic name) 1 (.read (.slot 0 0)) captured)) :
    Contracts.Statement .polynomialIdentity (.closure id) s := by
  intro arg admissible fuel result after he
  have same := successful_value s id name captured arg result after fuel h he
  subst result
  obtain ⟨ring,p,hp⟩ := admissible
  exact ⟨ring,p,p,hp,hp,Views.equivalent_refl p⟩

end Macaulean.M2.Verification.ProofJobs.Identity
