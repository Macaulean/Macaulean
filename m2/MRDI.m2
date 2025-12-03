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
    "addSaveMethod",
    "loadMRDI",
    "saveMRDI",

    -- symbols
    "UseID",
    "ToString",
    }

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

-- low-level unexported method
-- input: some object x
-- returns a pair (mrdi, refs)
-- mdri = hash table representing x (type & data only)
-- refs = list of hash tables representing x's refs (type & data only)
-- use addSaveMethod to define for a given class
toMRDI = method()

-- can't use addSaveMethod since "toMRDI params" would cause recursion error
toMRDI VisibleList := L -> (
    mrdis := toMRDI \ L;
    (
	hashTable {
	    "_type" => hashTable {
		"name" => toString class L,
		"params" => apply(mrdis, (mrdi, ref) -> mrdi#"_type")},
	    "data" => apply(#L, i ->
		?? (uuidsByThing#(L#i) ?? mrdis#i#0#"data"))},
	join(
	    flatten apply(mrdis, (mrdi, ref) -> ref),
	    for x in L list uuidsByThing#x ?? continue)))

addSaveMethod = method(Options => {UseID => false, Name => toString @@ class})
addSaveMethod(Type, Function) := o -> (T, dataf) -> (
    toMRDI T := x -> (
	if o.UseID then thingToUuid x;
	hashTable {
	    "_type" => o.Name x,
	    "data" => dataf x},
	{});
    T.UseID = o.UseID)
addSaveMethod(Type, Function, Function) := o -> (T, paramsf, dataf) -> (
    toMRDI T := x -> (
	if o.UseID then thingToUuid x;
	params := paramsf x;
	(mrdi, refs) := toMRDI params;
	if lookup(UseID, class params) then (
	    mrdi = thingToUuid params;
	    refs = append(refs, mrdi));
	(
	    hashTable {
		"_type" => hashTable {
		    "name" => o.Name x,
		    "params" => mrdi},
		"data" => dataf x},
	    refs));
    T.UseID = o.UseID)

addSaveMethod(Thing, toString)

addSaveMethod(QuotientRing,
    R -> (
	if isFinitePrimeField R then toString char R
	else error "not implemented yet"))

addSaveMethod(GaloisField,
    F -> hashTable {
	"char"   => toString F.char,
	"degree" => toString F.degree},
    UseID => true)

addSaveMethod(PolynomialRing,
    coefficientRing,
    R -> hashTable {
	"variables" => toString \ gens R},
    UseID => true)

-- TODO: maybe add to Core
-- or should we deal w/ the Number v. RingElement cases separately?
listForm Number := x -> {({}, x)}

addSaveMethod(RingElement,
    ring,
    f -> apply(listForm f,
	(exps, coeff) -> (toString \ exps, toString coeff)),
    Name => f -> "RingElement")

addSaveMethod(Ideal,
    ring,
    I -> apply(I_*, f -> (
	    apply(listForm f,
		(exps, coeff) -> (toString \ exps, toString coeff)))))

addSaveMethod(Matrix,
    ring,
    A -> apply(entries A, row -> (
	    apply(row, f -> (
		    apply(listForm f,
			(exps, coeff) -> (toString \ exps, toString coeff)))))))

saveMRDI = method(
    Dispatch => Thing,
    Options => {FileName => null, ToString => true})
saveMRDI Thing := o -> x -> (
    (mrdi, refs) := toMRDI x;
    r := (if o.ToString then toJSON else identity) merge(
	hashTable {
	    "_ns" => hashTable {
		"Macaulay2" => ("https://macaulay2.com", version#"VERSION")},
	    if lookup(UseID, class x) then "id" => thingToUuid x,
	    if #refs > 0 then "_refs" => hashTable apply(refs,
		ref -> ref => first toMRDI(
		    uuidToThing(ref, () -> error("unknown uuid: ", ref))))},
	mrdi,
	(x, y) -> error "unexpected key collision");
    if o.FileName =!= null then o.FileName << r << endl << close;
    r)

-------------
-- loading --
-------------

loadMethods = new MutableHashTable
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
-- inputs: string (namespace) and either a hash table (type & data) or uuid
-- outputs: a de-serialized M2 object
fromMRDI = method()
fromMRDI(String, HashTable) := (ns, r) -> (
    (name, params) := (
	if instance(r#"_type", HashTable)
	then (r#"_type"#"name", r#"_type"#"params")
	else (r#"_type", null));
    if not loadMethods#ns#?name then error ("unknown type: ", name);
    loadMethods#ns#name(params, ?? r#"data", fromMRDI_ns))
fromMRDI(String, String) := (ns, i) -> (
    if not isUuid i then error "expected a uuid"
    else uuidToThing(i, () -> (
	    if uuidsToCreate#?i
	    then fromMRDI(ns, remove(uuidsToCreate, i))
	    else error("unknown uuid: ", i))))

-- input function takes two args: params (de-serialized) & data
addLoadMethod = method()
addLoadMethod(String, String, Function) := (ns, type, f) -> (
    if not loadMethods#?ns then loadMethods#ns = new MutableHashTable;
    loadMethods#ns#type = f)

addLoadMethod("Macaulay2", "ZZ", (params, data, f) -> value data)
addLoadMethod("Macaulay2", "Ring", (params, data, f) -> (
	if data == "ZZ" then ZZ
	else if data == "QQ" then QQ
	else error "unknown ring"))
addLoadMethod("Macaulay2", "QuotientRing", (params, data, f) -> ZZ/(value data))
addLoadMethod("Macaulay2", "GaloisField", (params, data, f) -> (
	GF(value data#"char", value data#"degree")))
addLoadMethod("Macaulay2", "PolynomialRing", (params, data, f) -> (
	R := f params;
	R[Variables => data#"variables"]))

mrdiToPolynomial = (R, f) -> sum(f, term -> (
	(value term#1)*R_(value \ toList term#0)))
addLoadMethod("Macaulay2", "RingElement", (params, data, f) -> (
	mrdiToPolynomial(f params, data)))
addLoadMethod("Macaulay2", "Ideal", (params, data, f) -> (
	R := f params;
	ideal apply(data, f -> mrdiToPolynomial(R, f))))
addLoadMethod("Macaulay2", "Matrix", (params, data, f) -> (
	R := f params;
	matrix apply(data, row -> apply(row, f -> mrdiToPolynomial(R, f)))))

addLoadMethod("Oscar", "Base.Int", (params, data, f) -> value data)
addLoadMethod("Oscar", "ZZRingElem", (params, data, f) -> value data)
addLoadMethod("Oscar", "String", (params, data, f) -> data)
addLoadMethod("Oscar", "Float64", (params, data, f) -> value data)
addLoadMethod("Oscar", "ZZRing", (params, data, f) -> ZZ)
addLoadMethod("Oscar", "QQField", (params, data, f) -> QQ)
addLoadMethod("Oscar", "FiniteField", (params, data, f) -> (
	if params =!= null then error "not implemented yet"
	else ZZ/(value data)))

leanMonomialOrders = hashTable {
    "grevlex" => GLex
    -- TODO: add all of grind's various monomial orderings
    }
addLoadMethod("Lean", "Lean.Grind.CommRing.Poly", (params, data, f) -> (
	-- for now, just guess number of vars based on the highest index
	n := max flatten apply(last \ data, m -> first \ m) + 1;
	R := ZZ[vars(0..<n)];
	sum(data, mon -> mon#0 * product(mon#1, vp -> R_(vp#0)^(vp#1)))))

addListLoadMethod = method()
addListLoadMethod(String, String, Type) := (ns, type, T) -> (
    addLoadMethod(ns, type, (params, data, f) -> (
	    new T from apply(#params, i -> (
		    if instance(data#i, String) and isUuid data#i then f data#i
		    else f hashTable {
			"_type" => params#i,
			"data" => data#i})))))

addListLoadMethod("Macaulay2", "List", List)
addListLoadMethod("Macaulay2", "Sequence", Sequence)
addListLoadMethod("Macaulay2", "Array", Array)
addListLoadMethod("Oscar", "Tuple", Sequence)

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
checkMRDI "{\"_type\": {\"params\": \"ef9ecd1d-0a22-49d1-aeae-c02def9fc876\", \"name\": \"RingElement\"}, \"data\": [[[\"0\", \"0\", \"2\", \"0\"], \"1\"], [[\"0\", \"1\", \"0\", \"1\"], \"-1\"]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"ef9ecd1d-0a22-49d1-aeae-c02def9fc876\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"ef9ecd1d-0a22-49d1-aeae-c02def9fc876\", \"name\": \"Ideal\"}, \"data\": [[[[\"0\", \"0\", \"2\", \"0\"], \"1\"], [[\"0\", \"1\", \"0\", \"1\"], \"-1\"]], [[[\"0\", \"1\", \"1\", \"0\"], \"1\"], [[\"1\", \"0\", \"0\", \"1\"], \"-1\"]], [[[\"0\", \"2\", \"0\", \"0\"], \"1\"], [[\"1\", \"0\", \"1\", \"0\"], \"-1\"]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"ef9ecd1d-0a22-49d1-aeae-c02def9fc876\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"ef9ecd1d-0a22-49d1-aeae-c02def9fc876\", \"name\": \"Matrix\"}, \"data\": [[[[[\"0\", \"0\", \"2\", \"0\"], \"1\"], [[\"0\", \"1\", \"0\", \"1\"], \"-1\"]], [[[\"0\", \"1\", \"1\", \"0\"], \"1\"], [[\"1\", \"0\", \"0\", \"1\"], \"-1\"]], [[[\"0\", \"2\", \"0\", \"0\"], \"1\"], [[\"1\", \"0\", \"1\", \"0\"], \"-1\"]]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"ef9ecd1d-0a22-49d1-aeae-c02def9fc876\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
///

TEST ///
-- load Oscar objects
assert Equation(5, loadMRDI "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.5.0\"]},\"_type\":\"Base.Int\",\"data\":\"5\"}")
assert Equation(5, loadMRDI "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.5.0\"]},\"_type\":\"ZZRingElem\",\"data\":\"5\"}")
assert BinaryOperation(symbol ===, ZZ, loadMRDI "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.5.0\"]},\"_type\":\"ZZRing\"}")
assert BinaryOperation(symbol ===, QQ, loadMRDI "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.5.0\"]},\"_type\":\"QQField\"}")
///

TEST ///
-- Lean polynomial test
f = loadMRDI ////
{"data": [[3, []], [5, [[2, 3]]]],
 "_type": "Lean.Grind.CommRing.Poly",
 "_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.26.0-rc1"]}}
////
R = ring f
assert Equation(f, 3 + 5*R_2^3)
///

end
