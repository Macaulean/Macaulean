import Macaulean.Interpreter.Check
import MacauleanTest.FunctionCases

/-! Native M2 validates observable function results and independently parsed syntax.
No function pointer/handle is compared between processes. -/
namespace Macaulean.M2.FunctionM2Tests
open Lean Elab Command FunctionCases

-- Retain every mismatch instead of hiding later failures behind the first one.
run_cmd do
  let mut checked := 0
  for (source, expected) in successes do
    let leanOK := run source == .ok expected
    unless leanOK do
      logError m!"Lean disagrees on {repr source}: {(run source).toM2String}"
    match ← queryM2 source with
    | .ok (.ok actual) =>
      if actual == expected then
        if leanOK then checked := checked + 1
      else logError m!"native M2 disagrees on {repr source}: {repr actual} instead of {repr expected}"
    | .ok .error => logError m!"native M2 rejected positive case {repr source}"
    | .error e => logError m!"native query failed for {repr source}: {e}"
  unless checked == successes.length do
    throwError "only {checked}/{successes.length} positive function comparisons passed"
  logInfo m!"FUNCTION_VALUES_COMPLETE: {checked} independently checked typed results"

run_cmd do
  let mut checked := 0
  for (source, expected) in errors do
    let leanOK := run source == .error expected
    unless leanOK do
      logError m!"wrong Lean error on {repr source}: {(run source).toM2String}"
    match ← queryM2 source with
    | .ok .error => if leanOK then checked := checked + 1
    | .ok (.ok v) => logError m!"native M2 accepted error case {repr source}: {repr v}"
    | .error e => logError m!"native query failed for {repr source}: {e}"
  unless checked == errors.length do
    throwError "only {checked}/{errors.length} runtime-error controls passed"
  logInfo m!"FUNCTION_ERRORS_COMPLETE: {checked} independent runtime-error controls"

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

-- Assert M2's own concrete syntax, not a reparse by either interpreter frontend.
-- These shapes are independent of evaluation and of function-argument values.
run_cmd do
  let cases := #[
    ("x->x", "toString(t#0) == \"Arrow\" and toString(t#1#0) == \"Token\""),
    ("(x)->x", "toString(t#0) == \"Arrow\" and toString(t#1#0) == \"Parentheses\""),
    ("()->7", "toString(t#0) == \"Arrow\" and toString(t#1#0) == \"EmptyParentheses\""),
    ("(x,y)->x+y", "toString(t#0) == \"Arrow\" and toString(t#1#2#0) == \"Binary\" and toString(t#1#2#2#1) == \",\""),
    ("f g 3", "toString(t#0) == \"Adjacent\" and toString(t#2#0) == \"Adjacent\""),
    ("f(3)^2", "toString(t#0) == \"Adjacent\" and toString(t#2#0) == \"Binary\" and toString(t#2#2#1) == \"^\""),
    ("x:=7", "toString(t#0) == \"Binary\" and toString(t#2#1) == \":=\""),
    ("return 1,2", "toString(t#0) == \"Binary\" and toString(t#1#0) == \"Unary\" and toString(t#1#1#1) == \"return\" and toString(t#2#1) == \",\"")
  ]
  for (src, predicate) in cases do
    let quoted := (Json.str src).compress
    let query := s!"(t := (parse {quoted})#0; {predicate})"
    match ← queryM2 query with
    | .ok (.ok (.bool true)) => pure ()
    | .ok reply => throwError "native parser shape disagreed on {repr src}: {reply.toM2String}"
    | .error message => throwError "native parser query failed: {message}"
  logInfo m!"FUNCTION_PARSE_SHAPES_COMPLETE: {cases.size} independent structural assertions"
end Macaulean.M2.FunctionM2Tests
