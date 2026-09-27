import MacauleanTest.VerificationDSL

namespace Macaulean.M2.Verification.ImportTests
open Lean Elab Command
run_cmd do
  let index ← Index.get
  let session ← DSL.getSession
  unless index.entries.isEmpty && index.ledger.proposals.isEmpty && index.ledger.events.isEmpty do
    throwError "import inherited an interactive intent approval or semantic index"
  unless session.nextInput == 1 && session.env == prelude && session.outputs.isEmpty do
    throwError "import inherited M2 worksheet state"
  unless (Snapshot.theoryExt.getState (← getEnv)).isNone do
    throwError "import inherited another environment's cached theory seal"
  if (Parser.runParserCategory (← getEnv) `command "1+2").isOk then
    throwError "import silently activated M2 syntax"
  let inventory := Panel.inventory (← getEnv)
  unless (inventory.getObjValAs? String "proofStatus") == .ok "unattempted" do
    throwError "read-only inventory can claim proof evidence"
  logInfo "INTENT_IMPORT_ISOLATION_COMPLETE: no inherited approvals, index, cache or M2 state"
end Macaulean.M2.Verification.ImportTests
