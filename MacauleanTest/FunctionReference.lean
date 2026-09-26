import Macaulean.Interpreter.Check
import Macaulean.Interpreter.Input
import MacauleanTest.FunctionCases

/-! Development observations, replaced by assertions before final publication. -/
namespace Macaulean.M2.FunctionReference
open Lean Elab Command
run_cmd do
  for (src,expected) in FunctionCases.successes do
    unless run src == .ok expected do
      logError m!"FUNCTION_MISMATCH {repr src}: {(run src).toM2String}, expected {repr expected}"
  for src in #["2 = 3", "1 := 7", "{1}=2", "{1 2}", "1 2", "(x,1)=(2,3)"] do
    logInfo m!"STRING_AST {repr src}: {repr (parse src)}"
    match Input.parse src with
    | .ok p => logInfo m!"INPUT_AST {repr src}: {repr p.tree.toTerm}"
    | .error e => logInfo m!"INPUT_ERROR {repr src}: {e}"
end Macaulean.M2.FunctionReference
