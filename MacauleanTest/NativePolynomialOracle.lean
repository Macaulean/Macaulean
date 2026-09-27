import Macaulean.Interpreter.Check

/-!
Each polynomial oracle query has its own native M2 process. Ring construction,
local declarations, aliases and protected-symbol probes cannot contaminate the
next case. Only source evaluation is caught as an expected M2 error. Rendering,
encoding, transport, and process failures are never interpreted as algebra errors.
-/
namespace Macaulean.M2.NativePolynomialOracle
open Lean

private def encoder : String :=
  "m2ciEncode = v -> (cls := class v; " ++
  "if cls === ZZ then {\"ZZ\",toString v} " ++
  "else if cls === QQ then {\"QQ\",toString numerator v,toString denominator v} " ++
  "else if cls === Boolean then {\"Boolean\",toString v} " ++
  "else if cls === Nothing then {\"Nothing\"} " ++
  "else if cls === List or cls === Sequence then " ++
  "join({toString cls,toString (#v)},flatten apply(toList v,x -> m2ciEncode x)) " ++
  "else {\"unsupported\",toString cls});"

/-- Render only after evaluation has succeeded, outside the source-error handler. -/
private def runRendered (source result : String) : IO (List String) := do
  let script := "needsPackage \"JSON\";" ++ encoder ++
    "m2ciEvaluation = try {true,value " ++ (Json.str source).compress ++
    "} else {false};" ++
    "m2ciResult = if m2ciEvaluation#0 then (v := m2ciEvaluation#1;" ++ result ++
    ") else {\"error\"}; print(toJSON m2ciResult); exit 0;"
  let output ← IO.Process.output {
    cmd := "M2", args := #["-q","--silent","--no-readline","--stop","-e",script] }
  unless output.exitCode == 0 do
    throw <| IO.userError s!"native M2 process failed for {source} ({output.exitCode}): {output.stderr}"
  let json ← match Json.parse output.stdout with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"invalid native JSON for {source}: {e}\nstdout: {output.stdout}\nstderr: {output.stderr}"
  match fromJson? json with
  | .ok values => pure values
  | .error e => throw <| IO.userError s!"invalid native wire data for {source}: {e}\nJSON: {json.compress}"

def raw (source : String) (surface : Bool := false) : IO (List String) :=
  runRendered source (if surface then "{\"ok\",toString class v,toExternalString v}"
    else "join({\"ok\"},m2ciEncode v)")

/-- Check evaluation failure without requiring an encoder for successful values. -/
def raisesError (source : String) : IO Bool := do
  match ← runRendered source "{\"ok\"}" with
  | ["error"] => return true
  | ["ok"] => return false
  | wire => throw <| IO.userError s!"invalid native outcome for {source}: {repr wire}"

def query (source : String) : IO (Except String M2Reply) := do
  let wire ← raw source
  match M2Reply.ofWire wire with
  | .ok reply => return .ok reply
  | .error message =>
    return .error s!"{message}\nsource: {source}\nwire: {repr wire}"
end Macaulean.M2.NativePolynomialOracle
