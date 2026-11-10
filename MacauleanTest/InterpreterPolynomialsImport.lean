import MacauleanTest.InterpreterPolynomialsDSL

/-! Imports keep declarations and grammar definitions, not a worksheet's rings,
polynomials, captured state, transcript, or namespace activation. -/
open Lean Elab Command
run_cmd do
  let state ← Macaulean.M2.DSL.getSession
  unless state.heap.nextRing == 0 && state.nextInput == 1 && state.outputs.isEmpty do
    throwError "polynomial worksheet state leaked across an import"
  unless state.env == Macaulean.M2.prelude do throwError "polynomial bindings leaked across import"
  unless state.heap.cells.isEmpty && state.heap.functions.isEmpty && state.scope.count == 0 do
    throwError "captured polynomial values or local bindings leaked across import"
  if (Parser.runParserCategory (← getEnv) `command "QQ[x]").isOk then
    throwError "import activated bare polynomial commands"

open M2
#guard_msgs in
R = QQ[u,v];

/-- info: o2 = u^2 + 2*u*v + v^2 : QQ[u, v] -/
#guard_msgs in
(u+v)^2

/-- error: unbound variable 'saved' -/
#guard_msgs in
saved

/-- info: o4 = true : Boolean -/
#guard_msgs in
ring u === R

run_cmd do
  let s ← Macaulean.M2.DSL.getSession
  unless s.heap.nextRing == 1 do throwError "new module did not start a fresh ring counter"
