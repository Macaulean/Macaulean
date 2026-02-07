newPackage(
    "MRDI",
    Version => "0.1",
    Date => "November 2025",
    Headline => "serializing algebraic data with .mrdi files",
    Authors => {
	{
	    Name => "Doug Torrance",
	    Email => "dtorrance@piedmont.edu",
	    HomePage => "https://webwork.piedmont.edu/~dtorrance"
	    }},
    PackageImports => {"JSON"},
    Keywords => {"System"})

export {
    -- methods
    "addLoadMethod",
    "addNamespace",
    "addSaveMethod",
    "loadMRDI",
    "saveMRDI",

    -- symbols
    "Namespace",
    "ToString",
    "UseID",
    }

importFrom(Core, {
	"noMethod",
	"nullf"})

------------
-- saving --
------------

-- universally unique identifiers
-- https://www.rfc-editor.org/rfc/rfc9562
uuidsByThing = new MutableHashTable
thingsByUuid = new MutableHashTable
pad0 = (n, s) -> concatenate((n - #s):"0", s)
randnibbles = k -> pad0(k, changeBase(random 2^(4*k), 16))
thingToUuid = x -> uuidsByThing#x ??= (
    i := concatenate(
	randnibbles 8, "-", randnibbles 4, "-4", randnibbles 3, "-",
	changeBase(8 + random 4, 16), randnibbles 3, "-", randnibbles 12);
    thingsByUuid#i = x;
    i)
uuidToThing = (i, f) -> thingsByUuid#i ??= (
    x := f();
    uuidsByThing#x = i;
    x)
isUuid = i -> match("^[0-9a-fA-F]{8}-([0-9a-fA-F]{4}-){3}[0-9a-fA-F]{12}$", i)

namespaces =  new MutableHashTable
loadMethods = new MutableHashTable

addNamespace = method()
addNamespace(String, String, String) := (ns, url, v) -> (
    namespaces#ns = (url, v);
    loadMethods#ns = new MutableHashTable;
    Thing#{ns, UseID} = false;)

addNamespace("Macaulay2", "https://macaulay2.com", version#"VERSION")
addNamespace("Oscar", "https://github.com/oscar-system/Oscar.jl", "1.6.0")

-- low-level unexported function
-- input: ns: string (namespace)
--        x: the object to serialize
--        refs: mutable hash table (keys = uuids of refs)
-- output: hash table representing x (type & data only)
-- side effect: new refs are added to refs
-- use addSaveMethod to define for a given class
toMRDI = (ns, x, refs) -> (
    if (f := lookup({ns, toMRDI}, class x)) === null
    then error noMethod({ns, toMRDI}, x,)
    else f(x, refs))

useID = (ns, x) -> (
    if (u := lookup({ns, UseID}, class x)) === null
    then error noMethod({ns, UseID}, x,)
    else if not instance(u, Boolean)
    then error("expected ", {ns, UseID}, " for ", class x,
	" to be true or false")
    else u)

toMRDIorUuid = (ns, x, refs) -> (
    r := toMRDI(ns, x, refs);
    if useID(ns, x) then (
	i := thingToUuid x;
	refs#i = r;
	i)
    else r)

-- low-level unexported method
-- same interface as toMRDI, but attempts to separate out objects we'd like
-- to serialize from json-level objects that we're using to describe
-- other objects
processMRDI = method()
processMRDI(String, Thing, MutableHashTable) := toMRDIorUuid
processMRDI(String, String, MutableHashTable) := (ns, x, refs) -> x
processMRDI(String, Nothing, MutableHashTable) := (ns, x, refs) -> null
processMRDI(String, ZZ, MutableHashTable) := (ns, x, refs) -> toString x
processMRDI(String, List, MutableHashTable) := (ns, x, refs) -> (
    if class x === List then apply(x, y -> processMRDI(ns, y, refs))
    else toMRDIorUuid(ns, x, refs))
processMRDI(String, HashTable, MutableHashTable) := (ns, x, refs) -> (
    if class x === HashTable then applyValues(x, v -> processMRDI(ns, v, refs))
    else toMRDIorUuid(ns, x, refs))


addSaveMethod = method(Options => {
	UseID => false,
	Name => toString @@ class,
	Namespace => "Macaulay2"})

getType = method()
getType(Function, Thing) := (f, x) -> f x
getType(String,   Thing) := (s, x) -> s


addSaveMethod Type := o -> T -> (
    addSaveMethod(T, nullf, nullf, o))
addSaveMethod(Type, Function) := o -> (T, dataf) -> (
    addSaveMethod(T, nullf, dataf, o))
addSaveMethod(Type, Function, Function) := o -> (T, paramsf, dataf) -> (
    T#{o.Namespace, toMRDI} = (x, refs) -> (
	if o.UseID then thingToUuid x; -- save uuid
	params := processMRDI(o.Namespace, paramsf x, refs);
	data := processMRDI(o.Namespace, dataf x, refs);
	hashTable {
	    "_type" => (
		if params =!= null then hashTable {
		    "name" => getType(o.Name, x),
		    "params" => params}
		else getType(o.Name, x)),
	    if data =!= null then "data" => data});
    T#{o.Namespace, UseID} = o.UseID;)

addSaveMethod(ZZ, identity)

addSaveMethod(Ring,
    R -> (
	if isMember(R, {ZZ, QQ}) then toString R
	else error "not implemented yet"))

addSaveMethod(QuotientRing,
    R -> (
	if isFinitePrimeField R then char R
	else error "not implemented yet"))

addSaveMethod(GaloisField,
    F -> hashTable {
	"char"   => F.char,
	"degree" => F.degree},
    UseID => true)

addSaveMethod(PolynomialRing,
    coefficientRing,
    R -> hashTable {
	"variables" => toString \ gens R},
    UseID => true)

mrdiCoefficient = method()
mrdiCoefficient ZZ := identity
mrdiCoefficient QQ := x -> {numerator x, denominator x}

mrdiListForm = f -> apply(listForm f,
    (mon, coeff) -> {mon, mrdiCoefficient coeff})

addSaveMethod(RingElement,
    ring,
    mrdiListForm,
    Name => "RingElement")

addSaveMethod(Ideal,
    ring,
    I -> apply(I_*, mrdiListForm))

addSaveMethod(Matrix, ring, A -> apply(entries A, row -> mrdiListForm \ row))

saveMRDI = method(
    Dispatch => Thing,
    Options => {
	FileName => null,
	ToString => true,
	Namespace => "Macaulay2"})
saveMRDI Thing := o -> x -> (
    if not namespaces#?(o.Namespace)
    then error("unknown namespace: ", o.Namespace);
    refs := new MutableHashTable;
    mrdi := toMRDI(o.Namespace, x, refs);
    r := (if o.ToString then toJSON else identity) merge(
	hashTable {
	    "_ns" => hashTable {
		o.Namespace => namespaces#(o.Namespace)},
	    if useID(o.Namespace, x) then "id" => thingToUuid x,
	    if #refs > 0 then "_refs" => new HashTable from refs},
	mrdi,
	(x, y) -> error "unexpected key collision");
    if o.FileName =!= null then o.FileName << r << endl << close;
    r)

-------------
-- loading --
-------------

uuidsToCreate = new MutableHashTable

loadMRDI = method()
-- TODO: schema validation
loadMRDI String := loadMRDI @@ fromJSON
loadMRDI HashTable := r -> (
    ns := first keys r#"_ns";
    if not loadMethods#?ns then error("unknown namespace: ", ns);
    -- save info about refs we haven't created yet
    if r#?"_refs" then scanPairs(r#"_refs",
	(i, s) -> if not thingsByUuid#?i then uuidsToCreate#i = s);
    if r#?"id" then uuidToThing(r#"id", () -> fromMRDI(ns, r))
    else fromMRDI(ns, r))

-- unexported helper function
-- inputs: string (namespace) and object to de-serialize
-- outputs: a de-serialized M2 object
fromMRDI = method()
fromMRDI(String, HashTable) := (ns, r) -> (
    -- if it has a _type key, then it's an object to de-serialize
    if r#?"_type" then (
	(name, params) := (
	    if instance(r#"_type", HashTable)
	    then (r#"_type"#"name", r#"_type"#"params")
	    else (r#"_type", null));
	if not loadMethods#ns#?name then error ("unknown type: ", name);
	loadMethods#ns#name(
	    if params =!= null then fromMRDI(ns, params),
	    if r#?"data" then fromMRDI(ns, r#"data")))
    -- otherwise, de-serialize its values
    else applyValues(r, fromMRDI_ns))
fromMRDI(String, String) := (ns, s) -> (
    -- if the string is a uuid, then return the corresponding object
    if isUuid s then uuidToThing(s, () -> (
	    if uuidsToCreate#?s
	    then fromMRDI(ns, remove(uuidsToCreate, s))
	    else error("unknown uuid: ", s)))
    -- otherwise, just return the string
    else s)
fromMRDI(String, List) := (ns, x) -> apply(x, fromMRDI_ns)

-- input function takes two args: params (de-serialized) & data
addLoadMethod = method(Options => {Namespace => "Macaulay2"})
addLoadMethod(String, Function) := o -> (type, f) -> (
    if not loadMethods#?(o.Namespace)
    then error("unknown namespace: ", o.Namespace);
    loadMethods#(o.Namespace)#type = f)

addLoadMethod("ZZ", (params, data) -> value data)
addLoadMethod("Ring", (params, data) -> (
	if data == "ZZ" then ZZ
	else if data == "QQ" then QQ
	else error "unknown ring"))
addLoadMethod("QuotientRing", (params, data) -> ZZ/(value data))
addLoadMethod("GaloisField", (params, data) -> (
	GF(value data#"char", value data#"degree")))
addLoadMethod("PolynomialRing", (params, data) -> (
	params[Variables => data#"variables"]))

mrdiToCoefficient = method(Dispatch => Type)
mrdiToCoefficient ZZ := R -> value
mrdiToCoefficient QQ := R -> a -> value a#0 / value a#1

mrdiToPolynomial = (R, f) -> sum(f, term -> (
	((mrdiToCoefficient coefficientRing R) term#1)*R_(value \ toList term#0)))
addLoadMethod("RingElement", (params, data) -> (
	mrdiToPolynomial(params, data)))
addLoadMethod("Ideal", (params, data) -> (
	ideal apply(data, f -> mrdiToPolynomial(params, f))))
addLoadMethod("Matrix", (params, data) -> (
	matrix apply(data, row -> apply(row, f -> mrdiToPolynomial(params, f)))))

-----------
-- Oscar --
-----------

oscarRings = hashTable {
    ZZ => "ZZRing",
    QQ => "QQField",
    }
addSaveMethod(Ring,
    Name => R -> oscarRings#R ?? error "unknown ring",
    Namespace => "Oscar")

addSaveMethod(ZZ,
    x -> ZZ,
    toString,
    Name => "ZZRingElem",
    Namespace => "Oscar")

addSaveMethod(QQ,
    x -> QQ,
    x -> concatenate(toString numerator x, "//", toString denominator x),
    Name => "QQFieldElem",
    Namespace => "Oscar")

addLoadMethod("Base.Int", (params, data) -> value data, Namespace => "Oscar")
addLoadMethod("ZZRingElem",
    (params, data) -> value data,
    Namespace => "Oscar")
addLoadMethod("QQFieldElem",
    (params, data) -> (
	x := separate("//", data);
	if #x == 2 then value x#0 / value x#1
	else value x#0 / 1),
    Namespace => "Oscar")
addLoadMethod("String", (params, data) -> data, Namespace => "Oscar")
addLoadMethod("Float64", (params, data) -> value data, Namespace => "Oscar")
addLoadMethod("ZZRing", (params, data) -> ZZ, Namespace => "Oscar")
addLoadMethod("QQField", (params, data) -> QQ, Namespace => "Oscar")
addLoadMethod("FiniteField",
    (params, data) -> (
	if params =!= null then error "not implemented yet"
	else ZZ/(value data)),
    Namespace => "Oscar")

-------------------
-- documentation --
-------------------

beginDocumentation()

doc ///
  Key
    MRDI
  Headline
    serialization using the mrdi file format
  Description
    Text
      The MRDI package provides tools for serializing and deserializing
      mathematical objects in Macaulay2 using the
      @HREF("https://doi.org/10.1007/978-3-031-64529-7_25", "MRDI")@
      file format. MRDI leverages JSON as its underlying format,
      allowing for interoperability with other systems and persistent
      storage of complex algebraic and geometric objects.
    Example
      R = QQ[x,y,z,w]
      I = monomialCurveIdeal(R, {1,2,3})
      saveMRDI I
      loadMRDI oo
///

-----------
-- tests --
-----------

TEST ///
-- loadMRDI saveMRDI x should return x
checkMRDI = x -> assert BinaryOperation(symbol ===, loadMRDI saveMRDI x, x)
checkMRDI 5
checkMRDI ZZ
checkMRDI QQ
checkMRDI(ZZ/101)
checkMRDI GF(2, 3)
checkMRDI(QQ[x])
checkMRDI(QQ[x][y][z])
R = QQ[x,y,z,w]
I = monomialCurveIdeal(R, {1, 2, 3})
checkMRDI I_0
checkMRDI I
checkMRDI gens I
///

-* code to generate strings for the next test:

printWidth = 0
getFormattedMRDI = x -> (
    format replace(regexQuote version#"VERSION", "@VERSION@", saveMRDI x))
scan({
	5,
	ZZ,
	QQ,
	ZZ/101,
	GF(2, 3),
	QQ[x],
	QQ[x][y][z],
	(R = QQ[x,y,z,w]; I = monomialCurveIdeal(R, {1, 2, 3}); I_0),
	I,
	gens I
	}, x -> << "checkMRDI " << getFormattedMRDI x << endl)

*-

TEST ///
-- saveMRDI loadMRDI x should return x (possibly up to reordering of elements)
needsPackage "JSON"
checkMRDI = x -> (
    x = replace("@VERSION@", version#"VERSION", x);
    y := saveMRDI loadMRDI x;
    assert BinaryOperation(symbol ===, fromJSON x, fromJSON y))
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"ZZ\", \"data\": \"5\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"Ring\", \"data\": \"ZZ\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"Ring\", \"data\": \"QQ\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"QuotientRing\", \"data\": \"101\"}"
checkMRDI "{\"_type\": \"GaloisField\", \"data\": {\"degree\": \"3\", \"char\": \"2\"}, \"id\": \"366eef8c-095b-4675-bc4c-c815a6706f52\", \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}}"
checkMRDI "{\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\"]}, \"id\": \"31292984-9503-4034-9a78-7badbc3d5710\", \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}}"
checkMRDI "{\"_type\": {\"params\": \"8731803f-89bd-4ff7-a599-79375b33cf4c\", \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"z\"]}, \"id\": \"27447205-6c41-4ed5-91ba-f7b96c0a65ce\", \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"8731803f-89bd-4ff7-a599-79375b33cf4c\": {\"_type\": {\"params\": \"81e005bb-a348-423a-a627-e96ff29a3597\", \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"y\"]}}, \"81e005bb-a348-423a-a627-e96ff29a3597\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\", \"name\": \"RingElement\"}, \"data\": [[[\"0\", \"0\", \"2\", \"0\"], [\"1\", \"1\"]], [[\"0\", \"1\", \"0\", \"1\"], [\"-1\", \"1\"]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\", \"name\": \"Ideal\"}, \"data\": [[[[\"0\", \"0\", \"2\", \"0\"], [\"1\", \"1\"]], [[\"0\", \"1\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"1\", \"1\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"2\", \"0\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"1\", \"0\"], [\"-1\", \"1\"]]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\", \"name\": \"Matrix\"}, \"data\": [[[[[\"0\", \"0\", \"2\", \"0\"], [\"1\", \"1\"]], [[\"0\", \"1\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"1\", \"1\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"2\", \"0\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"1\", \"0\"], [\"-1\", \"1\"]]]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
///

TEST ///
-- save/load Oscar objects
checkMRDI = x -> assert BinaryOperation(symbol ===,
    loadMRDI saveMRDI(x, Namespace => "Oscar"), x)
checkMRDI ZZ
checkMRDI QQ
checkMRDI 5
checkMRDI(1/2)
///

end
