import MacauleanTest.InterpreterDSL

/-!
A different module must not inherit the imported worksheet's variables,
input counter, or output history. It must not inherit the scoped syntax either.
-/

open Lean Elab Command

run_cmd do
  let state ← Macaulean.M2.DSL.getSession
  unless state.nextInput == 1 && state.outputs.isEmpty do
    throwError "import leaked the worksheet's input counter or output history"
  unless state.env == Macaulean.M2.prelude do
    throwError "import leaked the worksheet's M2 variables"
  if (Parser.runParserCategory (← getEnv) `command "1 + 2").isOk then
    throwError "import implicitly enabled the M2 language"

open M2

/-- info: o1 = 3 : ZZ -/
#guard_msgs in
1 + 2

-- Previously assigned in the imported test module, but absent in this session.
/-- error: unbound variable 'secret' -/
#guard_msgs in
secret

/-- info: o3 = 5/6 : QQ -/
#guard_msgs in
1/2 + 1/3
