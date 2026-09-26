import Macaulean.Interpreter.Parser
import Macaulean.Interpreter.Runtime

namespace Macaulean.M2
inductive Outcome where
  | parseError (msg : String)
  | error (e : Error)
  | ok (v : Value)
  deriving Repr, DecidableEq, Inhabited

/-- Execute with an explicit evaluation-depth budget; exhaustion is never success. -/
def runWithFuel (fuel : Nat) (source : String) : Outcome :=
  match parse source with
  | .error message => .parseError message
  | .ok term => match Runtime.evaluate term (fuel := fuel) with
    | .error error => .error error | .ok result => .ok result.value

def run (source : String) : Outcome := runWithFuel Runtime.defaultFuel source
end Macaulean.M2
