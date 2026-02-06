-- TODO: implement json schema validation in M2 (probably not easy!)

needsPackage "Python"
needsPackage "MRDI"
needsPackage "JSON"
needs "lean-mrdi.m2"

jsonschema = import "jsonschema"
schema = fromJSON last splitWWW getWWW "https://zenodo.org/records/12723387/files/mrdi.json"
val = (x, ns) -> (
    mrdi := saveMRDI(x, Namespace => ns, ToString => false);
    assert try jsonschema@@validate(mrdi, schema) then true else false)

val(5, "Macaulay2")
val(ZZ, "Macaulay2")
val(QQ, "Macaulay2")
val(ZZ/101, "Macaulay2")
val(GF(2, 3), "Macaulay2")
val(QQ[x], "Macaulay2")
val(QQ[x][y][z], "Macaulay2")
R = QQ[x,y,z,w]
I = monomialCurveIdeal(R, {1,2,3})
val(I_0, "Macaulay2")
val(I, "Macaulay2")
val(gens I, "Macaulay2")
R = QQ[x,y]
val(1/2*x + 1/2*y, "Lean")

saveMRDI(x, Namespace => "Lean", ToString => false)
jsonschema@@validate(oo, schema)
