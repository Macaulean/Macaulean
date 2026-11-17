import Macaulean.Verification.ExecutionEffects
import Macaulean.Interpreter.GCD.Execution
import Macaulean.Verification.RowProgram

/-! Effect contracts for the actual search and row helper source bodies. -/
namespace Macaulean.M2.Verification.ReductionEffects
open Lexical Macaulean.M2.Runtime GCD.Execution ExecutionEffects

private theorem ro_nil : ∀ e ∈ ([] : List Code), ReadOnly names e := by simp
private theorem ro_cons (head : ReadOnly names code)
    (tail : ∀ e ∈ codes, ReadOnly names e) : ∀ e ∈ code::codes, ReadOnly names e := by
  intro e he
  rcases List.mem_cons.mp he with eq | mem
  · subst e; exact head
  · exact tail e mem

def selectorCallees := ["m2gbReducer", "leadMonomial", "m2MonomialDivides"]

theorem selector_readOnly : ReadOnly selectorCallees reducerBody := by
  unfold reducerBody localVar globalVar
  repeat
    first
    | exact ReadOnly.read
    | exact ReadOnly.int
    | apply ReadOnly.ifElse
    | apply ReadOnly.unop
    | apply ReadOnly.binop
    | apply ReadOnly.globalCall
    | apply ReadOnly.sequence
    | apply ro_cons
    | exact ro_nil
    | decide

theorem selector_safe (fuel : Nat) (arg : Value) (s : State) (globals : PreludeBindings s) :
    Safe s (call fuel (.algebra (.library "m2gbReducer")) arg s) := by
  apply library_safe "m2gbReducer" (.fixed ["h","G","j"]) 3 reducerBody
    selectorCallees reducer_source selector_readOnly _ rfl _ fuel arg s globals
  · intro name member
    simp only [selectorCallees, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    simp only [selectorCallees, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr ⟨.leadMonomial,rfl⟩
    · exact .inr ⟨.monomialDivides,rfl⟩

theorem selector_preserves (fuel : Nat) (arg result : Value) (s after : State)
    (globals : PreludeBindings s)
    (success : call fuel (.algebra (.library "m2gbReducer")) arg s = .ok (result,after)) :
    Extends s after := by
  have safe := selector_safe fuel arg s globals
  simpa only [success, Safe] using safe

theorem row_readOnly : ReadOnly ["m2gbSubtractRow"] RowProgram.body := by
  unfold RowProgram.body
  repeat
    first
    | exact ReadOnly.read
    | exact ReadOnly.int
    | apply ReadOnly.ifElse
    | apply ReadOnly.unop
    | apply ReadOnly.binop
    | apply ReadOnly.globalCall
    | apply ReadOnly.sequence
    | apply ReadOnly.listLit
    | apply ro_cons
    | exact ro_nil
    | decide

theorem row_safe (fuel : Nat) (arg : Value) (s : State) (globals : PreludeBindings s) :
    Safe s (call fuel (.algebra (.library "m2gbSubtractRow")) arg s) := by
  apply library_safe "m2gbSubtractRow" (.fixed ["row","c","other","i"]) 4 RowProgram.body
    ["m2gbSubtractRow"] RowProgram.source_body row_readOnly _ rfl _ fuel arg s globals
  · intro name member
    simp only [List.mem_singleton] at member
    subst name
    decide
  · intro name member
    simp only [List.mem_singleton] at member
    exact .inl member

end Macaulean.M2.Verification.ReductionEffects
