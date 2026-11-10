import Macaulean.Interpreter.Runtime

/-! # Pure worksheet sessions, including persistent lexical cells and closures -/
namespace Macaulean.M2
structure Output where
  input : Nat
  value : Value
  deriving Repr, Inhabited
structure Session where
  env : Env := prelude
  nextInput : Nat := 1
  outputs : List Output := []
  heap : Runtime.Heap := {}
  scope : Lexical.Scope := {}
  fileFrame : List Nat := []
  deriving Inhabited
structure Session.Result where
  session : Session
  outcome : Except Error Value
  output : Option Output
  warnings : List String := []

def Session.evaluate (s : Session) (term : Term) (fuel : Nat := Runtime.defaultFuel) :=
  Runtime.evaluate term ⟨s.env, s.heap⟩ s.scope s.fileFrame fuel

/-- Inspect visible file-local bindings before the global environment. -/
def Session.lookup (s : Session) (name : String) : Option Value :=
  match s.scope.names.lookup name with
  | some i => do
    let cell ← s.fileFrame[i]?
    s.heap.cells[cell]?
  | none => s.env.lookup name

/-- A failed input rolls back global and captured-cell writes together. -/
def Session.step (s : Session) (term : Term) (silent := false)
    (fuel : Nat := Runtime.defaultFuel) : Session.Result :=
  match s.evaluate term fuel with
  | .error error =>
    ⟨{ s with nextInput := s.nextInput + 1 }, .error error, none, []⟩
  | .ok result =>
    let value := result.value
    let output := if silent || value == .null then none else some ⟨s.nextInput, value⟩
    let outputs := match output with | none => s.outputs | some o => o :: s.outputs
    let next : Session := {
      env := result.state.env, heap := result.state.heap, scope := result.scope,
      fileFrame := result.fileFrame, nextInput := s.nextInput + 1, outputs }
    ⟨next, .ok value, output, result.warnings⟩
end Macaulean.M2
