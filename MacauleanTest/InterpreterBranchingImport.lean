import MacauleanTest.InterpreterBranchingDSL

open Lean Elab Command

run_cmd do
  let state ← Macaulean.M2.DSL.getSession
  unless state.env == Macaulean.M2.prelude do throwError "worksheet bindings escaped the module"
  unless state.nextInput == 1 && state.outputs.isEmpty do throwError "worksheet history escaped the module"
  if (Parser.runParserCategory (← getEnv) `command "if true then 7").isOk then
    throwError "import activated M2 command syntax"

open M2

#guard_msgs in
if false then 1/0

/-- info: o2 = 7 : ZZ -/
#guard_msgs in
if true then 7 else 1/0

/-- error: unbound variable 'magnitude' -/
#guard_msgs in
magnitude

/-- info: o4 = true : Boolean -/
#guard_msgs in
not false and true
