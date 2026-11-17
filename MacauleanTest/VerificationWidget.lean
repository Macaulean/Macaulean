import Macaulean.Verification.Panel

/-! Run the exact embedded widget JavaScript under a Node component harness.
Node is a test dependency only; production M2 execution and intent commands do
not start external processes. A browser-rendering claim is not made by this test. -/
open Lean Elab Command in
run_cmd do
  let out ← IO.Process.output {
    cmd := "node"
    args := #["--test", "scripts/intent-widget.test.mjs"] }
  unless out.exitCode == 0 do
    throwError "InfoView widget component tests failed ({out.exitCode}):\n{out.stdout}\n{out.stderr}"
  logInfo out.stdout
  logInfo "INTENT_WIDGET_COMPONENT_COMPLETE: eight tests of review, revision changes, source insertion and failure handling"
