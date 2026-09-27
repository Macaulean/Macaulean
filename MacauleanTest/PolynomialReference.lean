import MacauleanTest.NativePolynomialOracle

/-! Fresh-process assertions for native zero conventions and unsupported classes. -/
open Lean Elab Command Macaulean.M2
run_cmd do
  for (source,expected) in [
    ("R=QQ[x,y];leadCoefficient(0_R)", ["ok","QQ","0/1"]),
    ("R=QQ[x,y];leadTerm(0_R)", ["ok","R","0"]),
    ("R=QQ[x,y];leadMonomial(0_R)", ["error"]),
    ("R=QQ[x];R==R", ["error"]),
    ("R=QQ[x];coefficientRing R==QQ", ["error"]),
    ("x=3;R=QQ[x];gens R", ["ok","List","{p_0,p_1,p_2}"]),
    ("local x;R=QQ[x];numgens R", ["ok","ZZ","0"]),
    ("R=QQ[x,y];old=x+y;QQ[old]", ["error"]),
    ("x=2;QQ[x,y]", ["error"])
  ] do
    let actual ← NativePolynomialOracle.raw ("(" ++ source ++ ")") true
    unless actual == expected do throwError "native reference changed: {source}: {repr actual}"
  logInfo "POLYNOMIAL_REFERENCE_COMPLETE: 9 fresh-process native assertions"
