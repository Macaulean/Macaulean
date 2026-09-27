import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Check

namespace Macaulean.M2.PolynomialSmoke
open Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

run_cmd do
  for source in #[
    "R=QQ[x,y];x^2-y",
    "R=QQ[x,y];I=ideal(x^2-y,x*y-1);gens gb I",
    "R=QQ[x,y];I=ideal(x^2-y,x*y-1);G=gb I;gens I*getChangeMatrix G==gens G",
    "R=QQ[x,y];G=gb ideal(x^2-y,x*y-1);(x^3-1)%G",
    "R=QQ[x,y];gens gb ideal(0_R)",
    "R=QQ[x,y];gens gb ideal(x,1-x)"
  ] do
    match run source with
    | .ok v => logInfo m!"POLYNOMIAL_SMOKE {repr source}: {v.toM2String}"
    | result => throwError "polynomial/DSL smoke failure {repr source}: {result.toM2String}"

-- Temporary focused diagnostics distinguish construction of an Option from
-- actually reducing the normalized terms and their rational coefficients.
private def r : Algebra.Ring := ⟨0,["x"],[none]⟩
private def x := Algebra.Poly.indeterminate r 0
private def one := Algebra.Poly.constant r 1
example : one.isZero = false := by decide +kernel
example : x.data.terms.map (fun t => t.monomial.powers) = [[1]] := by decide +kernel
example : (x.add one).map (fun p => p.data.terms.length) = some 2 := by decide +kernel
#reduce (x.add one).map (fun p => p.data.terms.map (fun t => t.monomial.powers))
#reduce (x.add one).map (fun p => p.data.terms.map (fun t => t.coefficient.num))
#reduce run "rr=QQ[px];listForm px"
#reduce run "rr=QQ[px];listForm (px+1)"

run_cmd do
  for source in #[
    "numgens QQ[]", "numgens (QQ[])", "numgens QQ[probeVar]", "numgens (QQ[probeOther])",
    "(rr:=QQ[probeZero];listForm ((0_rr)^(-1)))",
    "(rr:=QQ[probeZero];listForm ((0_rr)^(-2)))",
    "(rr:=QQ[probeZero];listForm ((2_rr)^(-2)))"
  ] do
    match ← queryM2 source with
    | .error error => logInfo m!"POLYNOMIAL_BOUNDARY {repr source}: transport error {error}"
    | .ok .error => logInfo m!"POLYNOMIAL_BOUNDARY {repr source}: native error"
    | .ok (.ok v) => logInfo m!"POLYNOMIAL_BOUNDARY {repr source}: {v.toM2String} : {v.className}"
end Macaulean.M2.PolynomialSmoke
