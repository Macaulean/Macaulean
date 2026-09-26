import Macaulean.Interpreter.Check
import MacauleanTest.FunctionCases

/-! Native M2 validates observable function results and independently parsed syntax.
No function pointer/handle is compared between processes. -/
namespace Macaulean.M2.FunctionM2Tests
open Lean Elab Command FunctionCases

run_cmd do
  logInfo m!"FUNCTION_VALUES: {successes.length} explicit typed results"
  for (source, expected) in successes do
    unless run source == .ok expected do
      throwError "Lean disagrees on {repr source}: {(run source).toM2String}"
    match ← queryM2 source with
    | .ok (.ok actual) =>
      unless actual == expected do
        throwError "native M2 disagrees on {repr source}: {repr actual} instead of {repr expected}"
    | .ok .error => throwError "native M2 rejected positive case {repr source}"
    | .error e => throwError "native query failed: {e}"

run_cmd do
  logInfo m!"FUNCTION_ERRORS: {errors.length} independent runtime-error controls"
  for (source, expected) in errors do
    unless run source == .error expected do
      throwError "wrong Lean error on {repr source}: {(run source).toM2String}"
    match ← queryM2 source with
    | .ok .error => pure ()
    | .ok (.ok v) => throwError "native M2 accepted error case {repr source}: {repr v}"
    | .error e => throwError "native query failed: {e}"

-- Program results, not opaque closure identities, pass through the certificate API.
run_cmd do
  let src := "mk=x->y->{x+y,(x,y),1/1}; f=mk 7; f 8"
  let expected := Value.list [.zz 15,.sequence [.zz 7,.zz 8],.qq (mkRat 1 1)]
  match ← queryM2 src with
  | .ok (.ok v) => unless v == expected do throwError "native certificate result disagreed"
  | _ => throwError "native certificate query failed"
  addRunTheorem `Macaulean.M2.FunctionM2Tests.functionCertificate src (.ok expected)
    "Kernel-checked application of a closure with a captured lexical parameter."

example : run "mk=x->y->{x+y,(x,y),1/1}; f=mk 7; f 8" =
    .ok (.list [.zz 15,.sequence [.zz 7,.zz 8],.qq (mkRat 1 1)]) := functionCertificate

-- Additional native-only structural observations; assertions will pin their shapes.
run_cmd do
  for src in #["x->x", "(x)->x", "()->7", "(x,y)->x+y", "f g 3", "f(3)^2", "x:=7", "return 1,2"] do
    let quoted := (Json.str src).compress
    -- `parse` is M2's own parser, not our DSL/string parser.
    let query := s!"toString ((parse {quoted})#0)"
    let m2 ← globalM2Server
    let reply : List String ← m2.sendRequest "evalValue" [query]
    logInfo m!"FUNCTION_PARSE {repr src}: {repr reply}"
end Macaulean.M2.FunctionM2Tests
