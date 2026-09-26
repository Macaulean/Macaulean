import Macaulean.Interpreter.Check
import MacauleanTest.FunctionCases

/-! Development observations. The completed extension replaces these with assertions. -/
namespace Macaulean.M2.FunctionReference
open Lean Elab Command
run_cmd do
  for (src,expected) in FunctionCases.successes do
    unless run src == .ok expected do
      logError m!"FUNCTION_MISMATCH {repr src}: {(run src).toM2String}, expected {repr expected}"
  for src in #["1 2", "{1 2}", "(x=1\nx+2)", "(1\n2)", "{1\n2}",
    "{1;2 3}", "(f=x->x; f not false)", "(x:=local y;x==x)",
    "(counter=0;maker=()->(counter=counter+1;x->x);maker() (counter=counter+1);counter)",
    "(counter=0;maker=()->(counter=counter+1;x->x);(maker()) (counter=counter+1);counter)"] do
    let m2 ← globalM2Server
    let reply : List String ← m2.sendRequest "evalValue" [src]
    logInfo m!"FUNCTION_EXTRA {repr src}: {repr reply}"
end Macaulean.M2.FunctionReference
