import Macaulean.Interpreter.Check

/-! Native local-token observations for the lexical-binding extension. -/
namespace Macaulean.M2.FunctionLocalReference
open Lean Elab Command

run_cmd do
  let server ← globalM2Server
  for src in #["local", "local;", "(local)", "(local;)",
      "f=(x,y)->(local; x)", "local x", "local if", "local +", "local 7",
      "(f=(x,y)->(local; x);f(2,3))", "(local; 7)"] do
    let quoted := (Json.str src).compress
    let probe := "try (p := parse " ++ quoted ++ "; v := value " ++ quoted ++
      "; {toExternalString p,toString class v,toExternalString v}) else {\"NATIVE_ERROR\"}"
    let response : String ← server.sendRequest "testMethod" [probe]
    logInfo m!"LOCAL_REFERENCE {repr src}: {response}"

end Macaulean.M2.FunctionLocalReference
