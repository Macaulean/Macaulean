import Macaulean.Interpreter.Check

/-! Early integration checks for the actual source-language algorithm. -/
open Lean Elab Command Macaulean.M2
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000
run_cmd do
  for (source,expected) in [
    ("R=QQ[x,y];I=ideal(x^2-y,x*y-1);G=gb I;{numgens G,(x^3-1)%G==0,gens I*getChangeMatrix G==gens G}",
      Value.list [.zz 3,.bool true,.bool true]),
    ("R=QQ[x];I=ideal(0*x);G=gb I;{numgens G,numRows getChangeMatrix G,numColumns getChangeMatrix G,gens I*getChangeMatrix G==gens G}",
      Value.list [.zz 0,.zz 1,.zz 0,.bool true]),
    ("R=QQ[x,y];I=ideal(x,x*y-1);G=gb I;{numgens G,(x+y)%G==0,gens I*getChangeMatrix G==gens G}",
      Value.list [.zz 1,.bool true,.bool true])
  ] do
    let actual := run source
    unless actual == .ok expected do throwError "Buchberger smoke failure: {source}\n{repr actual}"
  logInfo "BUCHBERGER_SMOKE_COMPLETE: nontrivial, zero, and unit ideals with provenance"
