import MacauleanTest.GCDCases
import MacauleanTest.NativePolynomialOracle

namespace Macaulean.M2.GCDNativeTests
open Lean Elab Command GCDTests
set_option maxRecDepth 50000
set_option maxHeartbeats 30000000

run_cmd do
  for (f,g,expected) in cases do
    -- Native M2's unit convention need not match ours; compare monic answers.
    let source := s!"(R=QQ[x];d=gcd({f},{g});if d==0 then listForm d else listForm(d/(leadCoefficient d)))"
    let .ok want := run s!"R=QQ[x];listForm({expected})"
      | throwError "invalid native GCD expected value"
    match ← NativePolynomialOracle.query source with
    | .ok (.ok actual) =>
      unless actual == want do
        throwError "native GCD mismatch: {source}\n{repr actual}\n{repr want}"
    | .ok .error => throwError "native GCD rejected: {source}"
    | .error error => throwError "native GCD transport failed: {error}"
  logInfo m!"GCD_NATIVE_COMPLETE: {cases.length} exact monic coefficient/exponent comparisons"

end Macaulean.M2.GCDNativeTests
