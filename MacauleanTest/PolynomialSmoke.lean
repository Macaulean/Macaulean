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
end Macaulean.M2.PolynomialSmoke
