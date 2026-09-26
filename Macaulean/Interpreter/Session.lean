import Macaulean.Interpreter.Eval

/-!
# Pure worksheet sessions

Each input is transactional under `evalTerm`; previous inputs survive later
errors. Inputs returning `null` have no output label, as in the M2 REPL, but
still advance the input counter and retain successful assignments.
-/

namespace Macaulean.M2

structure Output where
  input : Nat
  value : Value
  deriving Repr, Inhabited

structure Session where
  env : Env := prelude
  nextInput : Nat := 1
  outputs : List Output := []
  deriving Inhabited

structure Session.Result where
  session : Session
  outcome : Except Error Value
  output : Option Output

def Session.step (s : Session) (term : Term) (silent := false) : Session.Result :=
  match evalTerm term s.env with
  | .error error =>
    ⟨{ s with nextInput := s.nextInput + 1 }, .error error, none⟩
  | .ok (value, env) =>
    let output := if silent || value == .null then none else some ⟨s.nextInput, value⟩
    let outputs := match output with
      | none => s.outputs
      | some o => o :: s.outputs
    ⟨{ env, nextInput := s.nextInput + 1, outputs }, .ok value, output⟩

end Macaulean.M2
