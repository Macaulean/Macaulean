import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Check

namespace Macaulean.M2.PolynomialSmoke
open Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

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
example : (x.pow 3).termData = [(1,[3])] := by decide +kernel

run_cmd do
  for source in #["0_R", "1_R", "(0_R)", "denominator := 0", "denomGuard = 0"] do
    match Macaulean.M2.Input.parse source with
    | .ok p => logInfo m!"INPUT_TREE {source}: {repr p.tree.toTerm}"
    | .error error => logInfo m!"INPUT_ERROR {source}: {error}"
    match Lean.Parser.runParserCategory (← getEnv) `m2 source with
    | .ok _ => logInfo m!"CATEGORY_OK {source}"
    | .error error => logInfo m!"CATEGORY_ERROR {source}: {error}"

run_cmd do
  for source in #[
    "(rr:=QQ[pgx];old:=pgx;ss:=QQ[old];{ring old==rr,ring pgx==ss,ring old==ss,ring pgx==rr})",
    "(rr:=QQ[pgx];old:=pgx;ss:=QQ[old];{numgens ss,exponents old,exponents pgx})",
    "(rr:=QQ[pgx];listForm leadMonomial (0_rr))"
  ] do
    match ← queryM2 source with
    | .error error => logInfo m!"NATIVE_BOUNDARY {repr source}: transport error {error}"
    | .ok .error => logInfo m!"NATIVE_BOUNDARY {repr source}: native error"
    | .ok (.ok v) => logInfo m!"NATIVE_BOUNDARY {repr source}: {v.toM2String} : {v.className}"

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
