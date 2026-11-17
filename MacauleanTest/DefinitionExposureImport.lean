import MacauleanTest.DefinitionExposure

/-! Exported declarations survive imports; the live M2 session does not. -/
open DefinitionWorksheet

example : M2Generated.n = (7 : Int) := rfl
example : M2Generated.n.v2 = (9 : Int) := rfl
example : (M2Generated.gcd2 128 (.sequence [.zz 81,.zz 30])).map Prod.fst = .ok (.zz 3) := by decide
example : M2Generated.p.terms.length = 3 := by decide
example : useAdder = .ok (.zz 13) := by decide

/-- info: Except.ok (Macaulean.M2.Value.zz 49) -/
#guard_msgs in
#eval (M2Generated.square 32 (.zz 7)).map Prod.fst

run_cmd do
  let session ← Macaulean.M2.DSL.getSession
  unless session.heap.cells.isEmpty && session.heap.functions.isEmpty && session.nextInput == 1 do
    throwError "importing definitions leaked the live worksheet session"
  unless (← Macaulean.M2.DefinitionExposure.latest "square").isNone do
    throwError "importing definitions leaked the latest-name registry"

-- No namespace: automatically qualify declarations by the module name.
open M2
answer = 42;
example : MacauleanTest.DefinitionExposureImport.M2Generated.answer = (42 : Int) := rfl
