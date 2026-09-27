import MacauleanTest.InterpreterGroebnerDSL

/-! Import the definitions and library, never the worksheet's computed bases,
ring identities, heap cells, transcript, or active scoped command bridge. -/
open Lean Elab Command
run_cmd do
  let s ← Macaulean.M2.DSL.getSession
  unless s.nextInput == 1 && s.outputs.isEmpty && s.heap.nextRing == 0 &&
      s.heap.cells.isEmpty && s.heap.functions.isEmpty && s.fileFrame.isEmpty do
    throwError "Buchberger worksheet state leaked through an import"
  unless s.env == Macaulean.M2.prelude && s.scope.count == 0 do
    throwError "Buchberger worksheet bindings leaked through an import"
  if (Parser.runParserCategory (← getEnv) `command "gb I").isOk then
    throwError "import activated the scoped M2 command bridge"

open M2
#guard_msgs in
R = QQ[u];

/-- info: o2 = matrix{{u - 1}} : Matrix -/
#guard_msgs in
gens gb ideal(u^2-1,u-1)

/-- error: unbound variable 'saved' -/
#guard_msgs in
saved

/-- info: o4 = true : Boolean -/
#guard_msgs in
ring(gb ideal(u)) === R

run_cmd do
  let s ← Macaulean.M2.DSL.getSession
  unless s.heap.nextRing == 1 do throwError "import did not reset the ring counter"
  logInfo "BUCHBERGER_IMPORT_ISOLATION_COMPLETE"
