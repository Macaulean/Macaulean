import MacauleanTest.PolynomialReference
import Macaulean.Interpreter.Check

/-! Minimal kernel regressions for the failing sorting path. These are not VM tests. -/
open Lean Elab Command Macaulean.M2
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
example : Polynomials.normalized 2 [(2,[0,1]),(1,[1,0]),(-2,[0,1]),(0,[9,9])] =
    .ok [(1,[1,0])] := by decide +kernel
example : Polynomials.mul 2 [(1,[1,0]),(1,[0,1])] [(1,[1,0]),(-1,[0,1])] =
    .ok [(1,[2,0]),(-1,[0,2])] := by decide +kernel

-- Successful values need not have a wire encoder to be distinguished from errors.
run_cmd do
  for (source, expected) in [
    ("1/0", true), ("null", false), ("()", false),
    ("QQ[x]", false), ("x -> x", false)
  ] do
    let actual ← NativePolynomialOracle.raisesError source
    unless actual == expected do
      throwError "native outcome misclassified for {source}: {actual}"
  match ← NativePolynomialOracle.query "QQ[x]" with
  | .error message =>
    unless (message.splitOn "wire:").length > 1 do
      throwError "unsupported value diagnostic lost its raw reply: {message}"
  | .ok .error => throwError "unsupported successful ring was reported as an evaluation error"
  | .ok (.ok value) => throwError "unsupported successful ring was decoded as {repr value}"
  match ← NativePolynomialOracle.query "(null,())" with
  | .ok (.ok (.sequence [.null, .sequence []])) => pure ()
  | .ok (.ok value) => throwError "outcome wrapper changed a nested value: {repr value}"
  | .ok .error => throwError "nested value was reported as an evaluation error"
  | .error message => throwError "nested value protocol failed: {message}"

  -- This source evaluates successfully but sabotages its result encoder. The old
  -- broad try handler incorrectly returned the same reply as division by zero.
  let source := "(m2ciEncode = v -> error \"injected encoder failure\"; 7)"
  if ← NativePolynomialOracle.raisesError source then
    throwError "encoder-injection source itself did not evaluate successfully"
  let encodingFailed ← try
    let _ ← NativePolynomialOracle.raw source
    pure false
  catch _ => pure true
  unless encodingFailed do
    throwError "serialization failure was incorrectly accepted as a source error"
  logInfo "NATIVE_ORACLE_OUTCOMES_COMPLETE: source errors, unsupported values, nested values, and encoder-failure isolation"
