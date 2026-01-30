-- TODO: implement json schema validation in M2 (probably not easy!)

needsPackage "Python"
needsPackage "MRDI"
needsPackage "JSON"

jsonschema = import "jsonschema"
schema = fromJSON last splitWWW getWWW "https://www.oscar-system.org/schemas/mrdi.json"
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
