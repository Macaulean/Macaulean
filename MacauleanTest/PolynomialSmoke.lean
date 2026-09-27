import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Check

namespace Macaulean.M2.PolynomialSmoke
open Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option pp.proofs false

private def r : Algebra.Ring := ⟨0,["x"],[none]⟩
private def x := Algebra.Poly.indeterminate r 0
private def one := Algebra.Poly.constant r 1
example : one.isZero = false := by decide +kernel
example : x.data.terms.map (fun t => t.monomial.powers) = [[1]] := by decide +kernel
example : (x.add one).map (fun p => p.data.terms.length) = some 2 := by decide +kernel
example : (x.add one).map (fun p => p.data.terms.map (fun t => t.monomial.powers)) =
    some [[1],[0]] := by decide +kernel
example : (x.add one).map (fun p => p.data.terms.map (fun t => t.coefficient.num)) =
    some [1,1] := by decide +kernel
example : decide (x = x) = true := by decide +kernel
example : decide (x = one) = false := by decide +kernel
example : (x.mul x).map (fun p => p.data.terms.map (fun t => t.monomial.powers)) =
    some [[2]] := by decide +kernel

-- Temporary, small backend diagnostics (no whole-runtime expansion).
#reduce (Macaulean.Polynomial.sortTerms (x.data.terms ++ one.data.terms)).length
#reduce (Macaulean.Polynomial.coalesceTerms (x.data.terms ++ one.data.terms)).length
#reduce (Macaulean.Polynomial.mergeTerms x.data.terms one.data.terms).length
#reduce (Macaulean.Polynomial.mergeTerms_old x.data.terms one.data.terms).length
#reduce (x.data.terms[0]!.monomial.mul x.data.terms[0]!.monomial).powers
#print axioms Macaulean.Polynomial.mergeTerms
#print axioms Macaulean.Polynomial.mulTerms

run_cmd do
  for source in #["0_R", "1_R", "(0_R)", "2*x", "QQ[]"] do
    match Lean.Parser.runParserCategory (← getEnv) `m2 source with
    | .ok _ => logInfo m!"M2_CATEGORY_ACCEPTED {source}"
    | .error err => logInfo m!"M2_CATEGORY_ERROR {source}: {err}"

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
    | .ok _ => pure ()
    | result => throwError "polynomial/DSL smoke failure {repr source}: {result.toM2String}"
end Macaulean.M2.PolynomialSmoke
