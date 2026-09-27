import Macaulean.Macaulay2
import Lean

/-! Native reference probes; converted to assertions before this PR is completed. -/
open Lean Elab Command
run_cmd do
  let server ← globalM2Server
  for source in #[
    "(R=QQ[x,y]; exponents((x+y)^2))",
    "(R=QQ[x,y]; listForm((x+y)^2))",
    "(R=QQ[x,y]; gens R)",
    "(R=QQ[x,y]; entries gens ideal(x^2-y,x*y-1))",
    "(R=QQ[x,y]; leadCoefficient(0_R))",
    "(R=QQ[x,y]; leadMonomial(0_R))",
    "(R=QQ[x,y]; leadTerm(0_R))",
    "(R=QQ[x,y]; terms(0_R))",
    "(R=QQ[x,y]; x/2)",
    "(R=QQ[x,y]; x/(1/2))",
    "(R=QQ[x,y]; (x^2)/x)",
    "(R=QQ[x,y]; (2_R)^(-1))",
    "(R=QQ[x,y]; (x^2)//x)",
    "(R=QQ[x,y]; (x+y)//x)",
    "(R=QQ[x,y]; lcm(2*x^2,3*y))",
    "(R=QQ[x,y]; coefficient(x,x+y))",
    "(R=QQ[x,y]; coefficient(1_R,x+y+2))",
    "(R=QQ[x,y]; exponents(0_R))",
    "QQ[]", "QQ[x,x]",
    "(R=QQ[x];S=QQ[x];R===S)",
    "(local x;R=QQ[x];x)",
    "(f=x->(R=QQ[x];x);f 3)",
    "(R=QQ[x,y]; numgens ideal(x,x,y))",
    "(R=QQ[x,y]; ideal(0_R,0_R))",
    "(R=QQ[x,y]; degree(0_R))"
  ] do
    let reply : List String ← server.sendRequest "evalValue" [source]
    logInfo m!"POLYNOMIAL_REFERENCE {repr source}: {repr reply}"
