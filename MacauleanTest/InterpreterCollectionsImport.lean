import MacauleanTest.InterpreterCollectionsDSL

/-! Importing a worksheet does not import its variables, history, or open syntax. -/
open Lean Elab Command

run_cmd do
  let state ← Macaulean.M2.DSL.getSession
  unless state.env == Macaulean.M2.prelude && state.nextInput == 1 && state.outputs.isEmpty do
    throwError "import leaked collection worksheet state"
  if (Parser.runParserCategory (← getEnv) `command "{1,2}").isOk then
    throwError "import enabled collection commands"

open M2

/-- info: o1 = {1, (2, 3)} : List -/
#guard_msgs in
{1,(2,3)}

/-- error: unbound variable 'saved' -/
#guard_msgs in
saved

/-- info: o3 = () : Sequence -/
#guard_msgs in
()

#guard_msgs in
null

/-- info: o5 = {5/6} : List -/
#guard_msgs in
{1/2+1/3}
