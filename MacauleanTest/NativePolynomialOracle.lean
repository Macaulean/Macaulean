import Macaulean.Interpreter.Check

/-!
Each polynomial oracle query has its own native M2 process. Ring construction,
local declarations, aliases and protected-symbol probes cannot contaminate the
next case. Transport/process failures are not interpreted as algebra errors.
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

def raw (source : String) (surface : Bool := false) : IO (List String) := do
  let result := if surface then "{\"ok\",toString class v,toExternalString v}"
    else "join({\"ok\"},m2ciEncode v)"
  let script := "needsPackage \"JSON\";" ++ encoder ++
    "m2ciResult = try (v := value " ++ (Json.str source).compress ++ ";" ++ result ++
    ") else {\"error\"}; print(toJSON m2ciResult); exit 0;"
  let output ← IO.Process.output {
    cmd := "M2", args := #["-q","--silent","--no-readline","--stop","-e",script] }
  unless output.exitCode == 0 do
    throw <| IO.userError s!"native M2 process failed ({output.exitCode}): {output.stderr}"
  let json ← match Json.parse output.stdout with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"invalid native JSON: {e}\n{output.stdout}\n{output.stderr}"
  match fromJson? json with
  | .ok values => pure values
  | .error e => throw <| IO.userError s!"invalid native wire data: {e}"

def query (source : String) : IO (Except String M2Reply) := do
  return M2Reply.ofWire (← raw source)
end Macaulean.M2.NativePolynomialOracle
