import MacauleanTest.InterpreterFunctionsDSL

/-! Importing a worksheet must not import its closure heap or lexical bindings. -/
open Lean Elab Command

run_cmd do
  let state ← Macaulean.M2.DSL.getSession
  unless state.env == Macaulean.M2.prelude && state.nextInput == 1 && state.outputs.isEmpty do
    throwError "worksheet values or outputs leaked across a module boundary"
  unless state.heap.cells.isEmpty && state.heap.functions.isEmpty do
    throwError "imported captured cells or function handles"
  unless state.scope.count == 0 && state.scope.names.isEmpty && state.fileFrame.isEmpty do
    throwError "imported file-local bindings"
  if (Parser.runParserCategory (← getEnv) `command "x->x").isOk then
    throwError "import activated the scoped language"

open M2
#guard_msgs in
f = (x) -> x+1;

/-- info: o2 = 8 : ZZ -/
#guard_msgs in
f 7

#guard_msgs in
localValue := 20;

/-- info: o4 = 20 : ZZ -/
#guard_msgs in
localValue

/-- error: unbound variable 'makeCounter' -/
#guard_msgs in
makeCounter
