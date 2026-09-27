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

-- Temporary focused diagnostics: the compiled evaluator already passes the
-- smoke cases, but the kernel must execute the same polynomial operations.
private def r : Algebra.Ring := ⟨0,["x"],[none]⟩
#reduce (Algebra.Poly.constant r 1).isZero
#reduce (Algebra.Poly.indeterminate r 0).data.terms.map (fun t => t.monomial.powers)
#reduce ((Algebra.Poly.indeterminate r 0).dataIn r).isSome
#reduce ((Algebra.Poly.indeterminate r 0).add (Algebra.Poly.constant r 1)).isSome
#reduce decide (Algebra.Poly.constant r 1 = Algebra.Poly.constant r 1)
#print axioms Algebra.Poly.constant
#print axioms Algebra.Poly.add

run_cmd do
  for source in #[
    "numgens QQ[]", "numgens (QQ[])", "numgens QQ[probeVar]", "numgens (QQ[probeOther])",
    "(rr:=QQ[probeZero];listForm ((0_rr)^(-1)))",
    "(rr:=QQ[probeZero];listForm ((0_rr)^(-2)))",
    "(rr:=QQ[probeZero];listForm ((2_rr)^(-2)))"
  ] do
    let reply ← queryM2 source
    logInfo m!"POLYNOMIAL_BOUNDARY {repr source}: {repr reply}"
end Macaulean.M2.PolynomialSmoke
