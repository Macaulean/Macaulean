import MacauleanTest.GroebnerCases
import MacauleanTest.GroebnerChecks
import MacauleanTest.NativePolynomialOracle

/-! Native M2 and a separate Lean algebra implementation both check the result.
Only typed coefficient/exponent observations cross the process boundary. -/
namespace Macaulean.M2.GroebnerNativeTests
open Lean Elab Command GroebnerCases
set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

run_cmd do
  for c in systems do
    let start ← IO.monoMsNow
    let .ok (.algebra object) := run c.source
      | throwError "DSL gb failed for {c.name}: {repr (run c.source)}"
    match GroebnerChecks.check object with
    | .error error => throwError "independent algebra check failed for {c.name}: {error}"
    | .ok _ => pure ()
    let .ok actual := GroebnerChecks.observed object | throwError "not a basis"
    match ← NativePolynomialOracle.query c.observation with
    | .ok (.ok (.list expected)) =>
      unless GroebnerChecks.sameMultiset actual expected do
        throwError "native basis mismatch for {c.name}\nDSL: {repr actual}\nnative: {repr expected}"
    | .ok (.ok v) => throwError "wrong native observation class for {c.name}: {v.className}"
    | .ok .error => throwError "native gb failed for {c.name}"
    | .error error => throwError "native protocol failed for {c.name}: {error}"
    logInfo m!"BUCHBERGER_CASE_PASS: {c.name}; {actual.length} generators; {(← IO.monoMsNow)-start} ms"
  logInfo m!"BUCHBERGER_NATIVE_SYSTEMS_COMPLETE: {systems.length}; provenance, both containments, S-pairs and reducedness"

-- Fixed coefficient grid: nonlinear inputs and all signs. Native M2 supplies
-- the final canonical remainders; the DSL computes them using its own gb.
run_cmd do
  let coeffs : List Int := [-2,-1,0,1,2]
  for a in coeffs do
    for b in coeffs do
      let source := s!"(rr=QQ[px,py];gg=gb ideal(px^2-py,px*py-1);listForm((({a})*px^4+({b})*py^3+px*py)%gg))"
      let .ok actual := run source | throwError "DSL reduction grid failed: {source}"
      match ← NativePolynomialOracle.query source with
      | .ok (.ok expected) => unless actual == expected do
          throwError "native reduction-grid mismatch: {source}\n{repr actual}\n{repr expected}"
      | .ok .error => throwError "native reduction grid failed: {source}"
      | .error error => throwError "native reduction transport failed: {error}"
  logInfo "BUCHBERGER_NATIVE_REMAINDERS_COMPLETE: 25 exact coefficient/exponent comparisons"
end Macaulean.M2.GroebnerNativeTests
