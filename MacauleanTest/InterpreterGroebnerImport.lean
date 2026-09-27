import MacauleanTest.InterpreterGroebnerDSL

/-! Imported worksheets do not import ring identities, variable bindings,
computed bases, captured cells, or active M2 syntax. -/
open Lean Elab Command
run_cmd do
  let s ← Macaulean.M2.DSL.getSession
  unless s.nextInput == 1 && s.outputs.isEmpty && s.heap.nextRing == 0 do
    throwError "ring/transcript state leaked through an import"
  unless s.env == Macaulean.M2.prelude && s.heap.cells.isEmpty && s.heap.functions.isEmpty do
    throwError "polynomial worksheet heap leaked through an import"
  if (Parser.runParserCategory (← getEnv) `command "QQ[x,y]").isOk then
    throwError "import implicitly activated M2 syntax"

open M2
#guard_msgs in
R = QQ[x];
/-- info: o2 = matrix {{x}} : Matrix -/
#guard_msgs in
gens gb ideal(2*x)
/-- error: unbound variable 'G' -/
#guard_msgs in
G
