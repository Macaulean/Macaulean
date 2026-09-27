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
    ("x=2;QQ[x,y]", ["error"]),
    -- Native polynomial powering is totalized at zero; it is not inversion in
    -- the coefficient field. Inspect exact coefficients, not just the class.
    ("R=QQ[x];listForm((x-x)^(-1))", ["ok","List","{}"]),
    ("R=QQ[x];listForm((x-x)^(-2))", ["ok","List","{}"]),
    ("R=QQ[x,y];listForm((0_R)^(-3))", ["ok","List","{}"])
  ] do
    let actual ← NativePolynomialOracle.raw ("(" ++ source ++ ")") true
    unless actual == expected do throwError "native reference changed: {source}: {repr actual}"
  logInfo "POLYNOMIAL_REFERENCE_COMPLETE: 12 fresh-process native assertions"
