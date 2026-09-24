import Macaulean.Interpreter.Parser
import Macaulean.Interpreter.Eval

/-!
# Running Macaulay2 source
-/

namespace Macaulean.M2

/-- Outcome of running a program: a parse error, a runtime error, or a value. -/
inductive Outcome where
  | parseError (msg : String)
  | error (e : Error)
  | ok (v : Value)
  deriving DecidableEq, Repr, Inhabited

/-- Parse and evaluate Macaulay2 source. -/
def run (s : String) : Outcome :=
  match parse s with
  | .error msg => .parseError msg
  | .ok t =>
    match evalProgram t with
    | .ok v => .ok v
    | .error e => .error e

end Macaulean.M2
