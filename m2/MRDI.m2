-- MRDI package for Macaulay2
-- Copyright (C) 2025-2026 Doug Torrance

-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License
-- as published by the Free Software Foundation; either version 2
-- of the License, or (at your option) any later version.

-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with this program; if not, see <https://www.gnu.org/licenses/>.

-- This package was originally written for use by the Macaulean project and its
-- development was funded by Renaissance Philantropy's AI for Math Fund.
-- https://www.renaissancephilanthropy.org/ai-for-math-fund

newPackage(
    "MRDI",
    Version => "0.1",
    Date => "April 25, 2026",
    Headline => "serializing algebraic data with .mrdi files",
    Authors => {
	{
	    Name => "Doug Torrance",
	    Email => "dtorrance9@gatech.edu",
	    HomePage => "https://d-torrance.github.io"
	    }},
    PackageImports => {"JSON"},
    Keywords => {"System"})

export {
    -- classes
    "OnlyData",
    "OnlyType",
    "TypeAndParams",

    -- methods
    "addLoadMethod",
    "addNamespace",
    "addSaveMethod",
    "loadMRDI",
    "saveMRDI",
    "validateMRDI",

    -- symbols
    "Instance",
    "Namespace",
    "Params",
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
uuidsToCreate = new MutableHashTable

addNamespace = method()
addNamespace(String, String, String) := (ns, url, v) -> (
    namespaces#ns = {url, v};
    loadMethods#ns = new MutableHashTable;
    uuidsToCreate#ns = new MutableHashTable;
    Thing#{ns, UseID} = false;)

addNamespace("Macaulay2", "https://macaulay2.com", version#"VERSION")
addNamespace("Oscar", "https://github.com/oscar-system/Oscar.jl", "1.8.2")

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

-- evaluate the thunk that's stored under {ns, saveMRDI}
-- to get its type and data functions for serialization
getMRDIFuncs = (ns, x) -> (
    if (f := lookup({ns, saveMRDI}, class x)) === null
    then error noMethod({ns, saveMRDI}, x,)
    else f())

-- low-level unexported function
-- input: ns: string (namespace)
--        x: the object to serialize
--        refs: mutable hash table (keys = uuids of refs)
-- output: hash table representing x (type & data only)
-- side effect: new refs are added to refs
-- use addSaveMethod to define for a given class
toMRDI = (ns, x, refs) -> (
    (typef, dataf) := getMRDIFuncs(ns, x);
    (type, data) := (typef(x, refs), dataf(x, refs));
    hashTable {
        "_type" => type,
        if data =!= null then "data" => data})

useID = (ns, x) -> (
    if (u := lookup({ns, UseID}, class x)) === null
    then error noMethod({ns, UseID}, x,)
    else if not instance(u, Boolean)
    then error("expected ", {ns, UseID}, " for ", class x,
	" to be true or false")
    else u)

maybeUuid = (ns, x, refs) -> (
    if useID(ns, x) then (
        i := thingToUuid x;
        refs#i ??= toMRDI(ns, x, refs);
        i))

toMRDIorUuid = (ns, x, refs) -> (
    maybeUuid(ns, x, refs) ?? toMRDI(ns, x, refs))

OnlyType = new SelfInitializingType of BasicList
OnlyData = new SelfInitializingType of BasicList

-- low-level unexported method
-- same interface as toMRDI, but attempts to separate out objects we'd like
-- to serialize from json-level objects that we're using to describe
-- other objects
processMRDI = method()
processMRDI(String, Thing, MutableHashTable) := toMRDIorUuid
processMRDI(String, Boolean, MutableHashTable) :=
processMRDI(String, String,  MutableHashTable) := (ns, x, refs) -> x
processMRDI(String, Nothing, MutableHashTable) := (ns, x, refs) -> null
processMRDI(String, ZZ, MutableHashTable) := (ns, x, refs) -> toString x
processMRDI(String, List, MutableHashTable) := (ns, x, refs) -> (
    if class x === List then apply(x, y -> processMRDI(ns, y, refs))
    else toMRDIorUuid(ns, x, refs))
processMRDI(String, HashTable, MutableHashTable) := (ns, x, refs) -> (
    if class x === HashTable
    then applyPairs(x, (k, v) -> (processMRDI(ns, k, refs),
                                  processMRDI(ns, v, refs)))
    else toMRDIorUuid(ns, x, refs))
processMRDI(String, OnlyType, MutableHashTable) :=  (ns, x, refs) -> (
    i := maybeUuid(ns, x#0, refs);
    if i =!= null then refs#i#"_type"
    else (
        (typef,) := getMRDIFuncs(ns, x#0);
        typef(x#0, refs)))
processMRDI(String, OnlyData, MutableHashTable) := (ns, x, refs) -> (
    maybeUuid(ns, x#0, refs) ?? (
        (,dataf) := getMRDIFuncs(ns, x#0);
        dataf(x#0, refs)))

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
    typefun := (x, refs) -> (
        if o.UseID then thingToUuid x; -- save uuid
        name := getType(o.Name, x);
        params := processMRDI(o.Namespace, paramsf x, refs);
        if params =!= null then hashTable {
            "name" => name,
            "params" => params}
        else name);
    datafun := (x, refs) -> (
        if o.UseID then thingToUuid x; -- save uuid
        data := processMRDI(o.Namespace, dataf x, refs);
        if data =!= null then data);
    -- thunk that returns a pair of functions so that "methods" works
    T#{o.Namespace, saveMRDI} = () -> (typefun, datafun);
    T#{o.Namespace, UseID} = o.UseID;)
addSaveMethod(List) := o -> Ts -> (
    scan(Ts, T -> addSaveMethod(T, nullf, nullf, o)))
addSaveMethod(List, Function) := o -> (Ts, dataf) -> (
    scan(Ts, T -> addSaveMethod(T, nullf, dataf, o)))
addSaveMethod(List, Function, Function) := o -> (Ts, paramsf, dataf) -> (
    scan(Ts, T -> addSaveMethod(T, paramsf, dataf, o)))

-----------------------
-- saving M2 objects --
-----------------------

addSaveMethod({ZZ, Boolean, String}, identity)
addSaveMethod(QQ, x -> {numerator x, denominator x})

addSaveMethod(Ring,
    R -> (
	if isMember(R, {ZZ, QQ}) then toString R
	else error "not implemented yet"))

addSaveMethod(QuotientRing,
    R -> (
	if isFinitePrimeField R then char R
	else error "not implemented yet"))

addSaveMethod(GaloisField,
              F -> if F.degree > 1 then ambient ambient F,
              F -> (
                  if F.degree == 1 then F.char
                  else OnlyData {(ideal ambient F)_0}),
              UseID => true)

addSaveMethod(PolynomialRing,
    coefficientRing,
    R -> hashTable {
	"variables" => toString \ gens R},
    UseID => true)

addSaveMethod(RingElement,
              ring,
              f -> (
                  R := ring f;
                  if isFinitePrimeField R then f^ZZ
                  else if instance(R, GaloisField)
                  then apply(listForm f^(ambient R),
                             (mon, coeff) -> {mon, OnlyData {coeff}})
                  else apply(listForm f,
                             (mon, coeff) -> {mon, OnlyData {coeff}})),
              Name => "RingElement")

addSaveMethod(Ideal,
              ring,
              I -> apply(I_*, f -> OnlyData {f}))

addSaveMethod(Matrix,
              ring,
              A -> apply(entries A,
                         row -> apply(row,
                                      entry -> OnlyData {entry})))
addSaveMethod(List,
              x -> apply(x, y -> OnlyType {y}),
              x -> apply(x, y -> OnlyData {y}))

addSaveMethod(Set,
              x -> apply(elements x, y -> OnlyType {y}),
              x -> apply(elements x, y -> OnlyData {y}))

-------------
-- loading --
-------------

-- each TypeAndParams object is a hash table with two keys:
-- Type: type object itself
-- Params: the load method for deserializing an instance of the type
TypeAndParams = new SelfInitializingType of HashTable
protect Params

-- check if we've already deserialized the object
isJSON = x -> isMember(class x,
                       {String, List, HashTable, ZZ, RR, Boolean, Nothing})

new TypeAndParams from (String, ImmutableType, Thing) :=
new TypeAndParams from (String, Type, Thing) := (T, ns, type, params) -> (
    memo := if instance(type, ImmutableType) then type.cache else type;
    memo#{ns, TypeAndParams} ??= T {
        symbol Type => type,
        Params => params,
        Instance => x -> (
            if isJSON x
            then (
                inst := lookup({ns, Instance}, type);
                if inst =!= null
                then loadMethods#ns#inst(type#{ns, TypeAndParams}, x)
                else error("no 'Instance' declared for ", type))
            else x)})
new TypeAndParams from (String, String, Thing) := (T, ns, name, params) -> T {
    symbol Type => name,
    Params => params,
    Instance => x -> (
        if isJSON x
        then loadMethods#ns#name(params, x)
        else x)}

loadMRDI = method()
-- TODO: schema validation
loadMRDI String := loadMRDI @@ fromJSON
loadMRDI HashTable := r -> (
    ns := first keys r#"_ns";
    if not loadMethods#?ns then error("unknown namespace: ", ns);
    -- save info about refs we haven't created yet
    if r#?"_refs" then scanPairs(r#"_refs", (i, s) -> uuidsToCreate#ns#i ??= s);
    if r#?"id" then uuidToThing(r#"id", () -> fromMRDI(ns, r))
    else fromMRDI(ns, r))

-- unexported helper function
-- inputs: string (namespace) and object to de-serialize
--         Params: whether to possibly return a TypeAndParams object
-- outputs: a de-serialized M2 object
fromMRDI = method(Options => {Params => false})
fromMRDI(String, HashTable) := o -> (ns, r) -> (
    -- if it has a _type key, then it's an object to de-serialize
    if r#?"_type" then (
        (name, params) := (
            if instance(r#"_type", HashTable)
            then (r#"_type"#"name", r#"_type"#"params")
            else (r#"_type", null));
        if not loadMethods#ns#?name then error ("unknown type: ", name);
        x := loadMethods#ns#name(
            fromMRDI(ns, params, Params => true),
            fromMRDI(ns, ?? r#"data"));
        if o.Params and (instance(x, Type) or instance(x, ImmutableType))
        then TypeAndParams(ns, x, fromMRDI(ns, params, Params => true))
        else x)
    else if o.Params and r#?"name"
    then TypeAndParams(ns, r#"name",
                       if r#?"params"
                       then fromMRDI(ns, r#"params", Params => true))
    -- otherwise, de-serialize its values
    else applyValues(r, v -> fromMRDI(ns, v, o)))
fromMRDI(String, String) := o -> (ns, s) -> (
    -- if the string is a uuid, then return the corresponding object
    if isUuid s then (
        x := uuidToThing(s, () -> (
            if uuidsToCreate#ns#?s
            then fromMRDI(ns, uuidsToCreate#ns#s)
            else error("unknown uuid: ", s)));
        if o.Params and (instance(x, Type) or instance(x, ImmutableType))
        then TypeAndParams(
            ns, x, (
                type := uuidsToCreate#ns#s#"_type";
                if instance(type, HashTable) and type#?"params"
                then fromMRDI(ns, type#"params", Params => true)))
        else x)
    -- if o.Params = true, then it's probably a type name, e.g., "ZZ"
    else if o.Params then TypeAndParams(ns, s,)
    -- otherwise, just return the string
    else s)
fromMRDI(String, List) := o -> (ns, x) -> apply(x, y -> fromMRDI(ns, y, o))
fromMRDI(String, Boolean) := o -> (ns, x) -> x
fromMRDI(String, Nothing) := o -> (ns, x) -> null

-- input function takes two args: params (de-serialized) & data
addLoadMethod = method(Options => {Namespace => "Macaulay2",
                                   Instance => null})
addLoadMethod(String, Function) := o -> (type, f) -> (
    if not loadMethods#?(o.Namespace)
    then error("unknown namespace: ", o.Namespace);
    if o.Instance =!= null then (o.Instance)#{o.Namespace, Instance} = type;
    loadMethods#(o.Namespace)#type = f)
addLoadMethod(List, Function) := o -> (types, f) -> (
    scan(types, type -> addLoadMethod(type, f, o)))

------------------------
-- loading M2 objects --
------------------------

addLoadMethod({"Boolean", "String"},
              (params, data) -> data)
addLoadMethod("ZZ",
              (params, data) -> value data,
              Instance => ZZ)
addLoadMethod("QQ",
              (params, data) -> value data#0 / value data#1,
              Instance => QQ)
addLoadMethod("Ring",
              (params, data) -> (
                  if data == "ZZ" then ZZ
                  else if data == "QQ" then QQ
                  else error "unknown ring"))
addLoadMethod("QuotientRing", (params, data) -> ZZ/(value data))
addLoadMethod("GaloisField",
              (params, data) -> (
                  -- GF(p)
                  if instance(data, String) then GF value data
                  -- GF(p^n)
                  else (
                      f := params.Instance data;
                      GF(ring f / f))))
addLoadMethod("PolynomialRing",
              (params, data) -> params.Type[Variables => data#"variables"])

-- RingElement is a catch-all instance type for a bunch of different rings
loadRingElement = method()
loadRingElement PolynomialRing := R -> (
    R.cache.loadRingElement ??= ((params, data) -> (
        if #data == 0 then 0_R
        else sum(data, term -> times(
            params.Params.Instance term#1,
            R_(value \ toList term#0))))))
loadRingElement QuotientRing := R -> (
    R.cache.loadRingElement ??= (
        if isFinitePrimeField R
        then (params, data) -> (value data)_R
        else notImplemented()))
loadRingElement GaloisField := R -> (
    R.cache.loadRingElement ??= (
        if isFinitePrimeField R
        then (params, data) -> (value data)_R
        else (params, data) -> (
            if #data == 0 then 0_R
            else (params.Params.Instance data)_R)))

addLoadMethod("RingElement",
              (params, data) -> (loadRingElement(params.Type))(params, data),
              Instance => RingElement)
addLoadMethod("Ideal",
              (params, data) -> ideal apply(data, f -> params.Instance f))
addLoadMethod("Matrix",
              (params, data) -> matrix applyTable(data, f -> params.Instance f))

addLoadMethod("List", (params, data) -> apply(params, data, (T, x) -> T.Instance x))
addLoadMethod("Set", (params, data) -> set apply(params, data,
                                                 (T, x) -> T.Instance x))

-- for debugging w/ "methods"
LoadMethod = new SelfInitializingType of List
net LoadMethod := lookup(net, Sequence)
locate LoadMethod := x -> locate loadMethods#(x#0#0)#(x#1)
code LoadMethod := code @@ locate

importFrom(Core, "previousMethodsFound")
oldmethods = lookup(methods, List)
methods List := x -> (
    if #x == 2 and x#1 === loadMRDI then (
	previousMethodsFound = new NumberedVerticalList from (
	    if loadMethods#?(x#0) then (
		apply(keys loadMethods#(x#0), k -> LoadMethod(x, k)))
	    ?? {}))
    else oldmethods x)

-------------------------------------
-------------------------------------
--   ___   ___   ___    _    ____  --
--  / _ \ / __\ / __\  / \  |  _ \ --
-- | |_| |\__ \| |__  / ^ \ |  ´ / --
--  \___/ \___/ \___//_/ \_\|_|\_\ --
-------------------------------------
-------------------------------------

-- saving

addSaveMethod(Boolean,
              identity,
              Name => "Bool",
              Namespace => "Oscar")

addSaveMethod(String,
              identity,
              Namespace => "Oscar")

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
              x -> (
                  if (den := denominator x) == 1
                  then toString numerator x
                  else concatenate(toString numerator x, "//", toString den)),
              Name => "QQFieldElem",
              Namespace => "Oscar")

-- Oscar differentiates between univariate and multivariate polynomial rings,
-- but multivariate rings can have just 1 variable, so we just always use that
addSaveMethod(PolynomialRing,
    coefficientRing,
    R -> hashTable {"symbols" => toString \ gens R},
    Name => "MPolyRing",
    UseID => true,
    Namespace => "Oscar")

addSaveMethod(GaloisField,
              F -> if F.degree > 1 then ambient ambient F,
              F -> (
                  if F.degree == 1 then F.char
                  else OnlyData {(ideal ambient F)_0}),
              UseID => true,
              Namespace => "Oscar")

addSaveMethod(RingElement,
    ring,
    f -> apply(listForm f, mon -> {mon#0, OnlyData {mon#1}}),
    Name => "MPolyRingElem",
    Namespace => "Oscar")

addSaveMethod(List,
              x -> apply(x, y -> OnlyType {y}),
              x -> apply(x, y -> OnlyData {y}),
              Name => "Tuple",
              Namespace => "Oscar")

addSaveMethod(HashTable,
              x -> (
                  if class x =!= HashTable
                  then error "expected a HashTable object";
                  if #x == 0
                  then error "cannot obtain type info for empty hash table";
                  typeinfo := applyKeys(
                      x, class, (v1,v2) -> (
                          if class v1 === class v2
                          then v1
                          else error "expected values of the same type"));
                  if #typeinfo > 1
                  then error "expected keys of the same type";
                  (k, v) := (pairs select(1, x, y -> true))#0;
                  hashTable {
                      "key_params" => OnlyType {k},
                      "value_params" => OnlyType {v}}),
              x -> applyPairs(x, (k, v) -> (OnlyData {k}, OnlyData {v})),
              Name => "Dict",
              Namespace => "Oscar")

addSaveMethod(Set,
              x -> (
                  if #x == 0 then error "expected a nonempty set";
                  if #(class \ x) > 1
                  then error "expected elements of the same type";
                  OnlyType {first elements x}),
              x -> apply(elements x, y -> OnlyData {y}),
              Namespace => "Oscar")

-- only supported for Hom between free modules (matrix space)
addSaveMethod(Module,
              ring,
              M -> (
                  expr := formation M;
                  if expr === null or expr#0 =!= Hom
                  then error "expected a Hom module";
                  if not isFreeModule expr#1#0
                  then error "expected source of Hom module to be free";
                  if not isFreeModule expr#1#1
                  then error "expected target of Hom module to be free";
                  hashTable {
                      "ncols" => rank expr#1#0,
                      "nrows" => rank expr#1#1}),
              Name => "MatSpace",
              Namespace => "Oscar",
              UseID => true)
addSaveMethod(Matrix,
              f -> Hom(source f, target f),
              f -> applyTable(entries f, x -> OnlyData {x}),
              Name => "MatElem",
              Namespace => "Oscar")

-- loading

addLoadMethod("Bool",
              (params, data) -> (
                  if instance(data, String)
                  then value data -- basic v1
                  else data),     -- basic v2
              Namespace => "Oscar")
addLoadMethod("String", (params, data) -> data, Namespace => "Oscar")

addLoadMethod({"Base.Int", "Int8", "UInt8", "Int16", "UInt16", "Int32",
               "UInt32", "Int64", "UInt64", "Int128", "UInt128", "BigInt",
               "Float16", "Float32", "Float64"},
              (params, data) -> value data, Namespace => "Oscar")

addLoadMethod("ZZRingElem",
              (params, data) -> value data,
              Instance => ZZ,
              Namespace => "Oscar")
addLoadMethod("QQFieldElem",
              (params, data) -> (
                  x := separate("//", data);
                  if #x == 2 then value x#0 / value x#1
                  else value x#0 / 1),
              Instance => QQ,
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
addLoadMethod({"PolyRing", "MPolyRing"},
    (params, data) -> (
	-- TODO: handled indexed variables, e.g., x[1], x[2], x[3]
	params.Type[Variables => data#"symbols"]),
    Namespace => "Oscar")
addLoadMethod({"PolyRingElem", "MPolyRingElem"},
              (params, data) -> (loadRingElement(params.Type))(params, data),
              Namespace => "Oscar",
              Instance => RingElement)

-- containers
addLoadMethod("Vector",
              (params, data) -> apply(data, x -> params.Instance x),
              Namespace => "Oscar")
addLoadMethod("Tuple",
              (params, data) -> apply(params, data, (T, x) -> T.Instance x),
              Namespace => "Oscar")
addLoadMethod("Set",
              (params, data) -> set apply(data, x -> params.Instance x),
              Namespace => "Oscar")

addLoadMethod("Dict",
              (params, data) -> (
                  -- Oscar v1.4+
                  if params#?"key_params"
                  then applyPairs(data, (k, v) -> (
                      params#"key_params".Instance k,
                      params#"value_params".Instance v))
                  -- Oscar v1.1-1.3
                  else if params#?"key_type" and params#?"value_type"
                  then applyPairs(data, (k, v) -> (
                      params#"key_type".Instance k,
                      params#"value_type".Instance v))
                  -- Oscar v1.0
                  else applyPairs(data, (k, v) -> (
                      params#"key_type".Instance k,
                      params#k.Instance v))),
              Namespace => "Oscar")

addLoadMethod("Matrix",
              (params, data) -> matrix applyTable(data, f -> params.Instance f),
              Namespace => "Oscar")

addLoadMethod("MatSpace",
              (params, data) -> (
                  R := params.Type;
                  Hom(R^(value data#"ncols"), R^(value data#"nrows"))),
              Namespace => "Oscar")

addLoadMethod("MatElem",
              (params, data) -> matrix applyTable(data,
                                                f -> params.Params.Instance f),
              Namespace => "Oscar")

----------------
-- validating --
----------------

-- https://www.oscar-system.org/schemas/mrdi.json

-- all JSON objects must have keys as strings
validateObject = x -> scanKeys(x, k -> (
	if not instance(k, String)
	then error("expected all keys to be strings, but got ", k)))

validateData = method()
validateData Thing := x -> error("invalid data: ", x)
validateData Boolean :=
validateData Nothing :=
validateData String  := x -> null
validateData HashTable := x -> (
    validateObject x;
    scan({"_ns", "_type"},
         k -> if x#?k then error("data cannot have a '", k, "' key"));
    scanPairs(x, (k, v) -> (
	    if not match("^[a-zA-Z0-9_]*", k)
	    then error("expected an alphanumeric key, but got ", k);
	    validateData v)))
validateData List := x -> scan(x, validateData)
-- TODO: validate polymake schema

validateParams = method()
validateParams Thing := validateData
validateParams List := x -> scan(x, validateParams)
validateParams HashTable := x -> (
    validateObject x;
    if x#?"_type" then validateMRDI x
    else scanValues(x, validateParams))

validateMRDI = method()
validateMRDI Thing := x -> error("expected an object, but got a(n) ",
                                 synonym class x)
validateMRDI String := validateMRDI @@ fromJSON
validateMRDI HashTable := x -> (
    validateObject x;
    if not x#?"_type" then error "expected a '_type' key";
    if instance(x#"_type", String) then null
    else if instance(x#"_type", HashTable) then (
	validateObject x#"_type";
	if x#"_type"#?"name" then (
	    if not instance(x#"_type"#"name", String)
	    then error("expected value of 'name' to be a string"))
	else error "expected '_type' to have a 'name' key";
	if x#"_type"#?"params" then validateParams x#"_type"#"params")
    else error("expected value of '_type' to be a string or object");
    scan({"_ns", "_refs"}, k -> (
	    if x#?k then (
		if not instance(x#k, HashTable)
		then error("expected value of '", k, "' to be an object");
		validateObject x#k)));
    if x#?"_refs" then scanValues(x#"_refs", validateMRDI);
    if x#?"data" then validateData x#"data";
    if x#?"id" and not isUuid x#"id"
    then error("expected value of \"id\" to be a UUID"))

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
    The @EM "MRDI"@ package provides tools for serializing and deserializing
    mathematical objects in Macaulay2 using the MRDI file format, a JSON-based
    format for storing and sharing results in computer algebra without losing
    accuracy.  The format was developed as part of the
    @HREF("https://www.mardi4nfdi.de/",
	"Mathematics Research Data Initiative (MaRDI)")@
    and is described in the paper:

    Antony Della Vecchia, Michael Joswig, and Benjamin Lorenz,
    @HREF("https://doi.org/10.1007/978-3-031-64529-7_25",
	"A FAIR file format for mathematical software")@,
    @EM "Mathematical software—ICMS 2024"@, 234–244, Lecture Notes in
    Comput. Sci., 14749, Springer, Cham.

    Each serialized object carries a namespace (@TT "_ns"@) identifying
    the originating software system and version, a type descriptor
    (@TT "_type"@) that may include recursive parameters, the actual
    data, and optionally a set of references (@TT "_refs"@) keyed by
    UUIDs.

    The package can serialize and deserialize integers, rings
    (@TO ZZ@, @TO QQ@, finite prime fields, Galois fields), polynomial rings,
    ring elements, ideals, and matrices.  It can also load and save objects
    using the OSCAR namespace, enabling interoperability with the
    @HREF("https://www.oscar-system.org/", "OSCAR")@ computer algebra system.

    The namespace mechanism also makes it possible to define custom
    serialization formats for exchanging data with other software systems.
  Example
    R = QQ[x,y,z,w]
    I = monomialCurveIdeal(R, {1,2,3})
    s = saveMRDI I
    loadMRDI s
Subnodes
  saveMRDI
  loadMRDI
  Namespace
  validateMRDI
///

doc ///
Key
  saveMRDI
  (saveMRDI, Thing)
  [saveMRDI, FileName]
  [saveMRDI, Namespace]
  [saveMRDI, ToString]
  ToString
Headline
  serialize a Macaulay2 object to MRDI JSON format
Usage
  saveMRDI x
Inputs
  x:Thing
    a Macaulay2 object to serialize (must have a save method
    registered via @TO addSaveMethod@)
  FileName => String
    if given, the JSON output is written to this file
  Namespace => String
    the namespace to use for serialization
  ToString => Boolean
    if @TO true@, then the output is a JSON string;
    if @TO false@, then the output is @ofClass HashTable@ representing
    the JSON structure
Outputs
  :{String, HashTable}
Description
  Text
    This function serializes a Macaulay2 object into a JSON string following
    the MRDI file format specification.  The output includes a namespace
    (@TT "_ns"@) identifying the software system and its version, a type
    descriptor (@TT "_type"@), and the data.

    For parametric types such as @TO PolynomialRing@,
    @TO RingElement@, @TO Ideal@, and @TO Matrix@, the type
    descriptor includes a @TT "params"@ field referencing the
    parent ring.  Rings and other objects marked with
    @TO UseID@ are assigned UUIDs so that multiple objects
    sharing the same ring refer to it by UUID rather than
    repeating its full description.
  Text
    We may serialize a simple integer.
  Example
    saveMRDI 5
  Text
    We can also serialize a polynomial ring element.
  Example
    R = QQ[x,y,z];
    f = x^2 + y*z - 3*x
    saveMRDI f
  Text
    Ideals are serialized similarly.
  Example
    I = ideal(x^2 - y, y^2 - z)
    saveMRDI I
  Text
    The output can be written directly to a file using the @TO FileName@ option.
  Example
    fn = temporaryFileName() | ".mrdi"
    saveMRDI(f, FileName => fn)
    removeFile fn
  Text
    The @TO Namespace@ option selects a different namespace for
    serialization, such as OSCAR.
  Example
    saveMRDI(5, Namespace => "Oscar")
  Text
    Setting @TT "ToString => false"@ returns the hash table
    representation instead of a JSON string.
  Example
    saveMRDI(5, ToString => false)
  Text
    To see which types have built-in save methods for a given namespace,
    call @TO methods@ as follows.
  Example
    methods {"Macaulay2", saveMRDI}
    methods {"Oscar", saveMRDI}
  Text
    Additional types can be supported by calling @TO addSaveMethod@.
Caveat
  Not all Macaulay2 types have save methods defined.  Attempting
  to serialize an unsupported type will produce an error.
  Quotient rings other than finite prime fields are not yet
  supported.
Subnodes
  addSaveMethod
SeeAlso
  loadMRDI
///

doc ///
Key
  loadMRDI
  (loadMRDI, String)
  (loadMRDI, HashTable)
Headline
  deserialize a Macaulay2 object from MRDI format
Usage
  loadMRDI s
Inputs
  s:{String, HashTable}
    a JSON string in the MRDI file format or
    parsed JSON hash table (e.g., from @TO "JSON::fromJSON"@)
Outputs
  :Thing -- the deserialized Macaulay2 object
Description
  Text
    This method parses an MRDI-formatted JSON string (or hash table) and
    reconstructs the corresponding Macaulay2 object.  The namespace field
    (@TT "_ns"@) in the JSON determines which set of load methods is used for
    deserialization.

    This function handles the @TT "_refs"@ section of the JSON
    to reconstruct shared references via UUIDs.  For example,
    when an ideal and a ring element both refer to the same
    polynomial ring, the ring is constructed once and shared.
  Text
    A polynomial ring element can be round-tripped through the format.
  Example
    R = QQ[x,y,z,w];
    f = x^2 + y*z
    s = saveMRDI f
    g = loadMRDI s
    f === g
  Text
    The same works for ideals.
  Example
    I = monomialCurveIdeal(R, {1,2,3})
    s = saveMRDI I
    J = loadMRDI s
    I === J
  Text
    Objects can be loaded from a file as well using @TO get@.
  Example
    fn = temporaryFileName() | ".mrdi"
    saveMRDI(I, FileName => fn)
    J = loadMRDI get fn
    I === J
    removeFile fn
  Text
    A parsed hash table can also be passed directly, for instance
    when using @TT "ToString => false"@ with @TO saveMRDI@.
  Example
    h = saveMRDI(42, ToString => false)
    loadMRDI h
  Text
    The MRDI format supports cross-system interoperability.
    Objects serialized by the OSCAR computer algebra system
    can also be loaded.
  Example
    loadMRDI "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.5.0\"]},\"_type\":\"ZZRingElem\",\"data\":\"42\"}"
  Text
    To see which types have built-in load methods for a given namespace,
    call @TO methods@ as follows.
  Example
    methods {"Macaulay2", loadMRDI}
    methods {"Oscar", loadMRDI}
  Text
    Additional types can be supported by calling @TO addLoadMethod@.
Caveat
  If the JSON string references a namespace or type for which
  no load method has been registered, an error is produced.
  Use @TO addLoadMethod@ to register handlers for custom types
  and @TO addNamespace@ to register new namespaces.
Subnodes
  addLoadMethod
SeeAlso
  saveMRDI
///

doc ///
Key
  addSaveMethod
  (addSaveMethod, Type)
  (addSaveMethod, Type, Function)
  (addSaveMethod, Type, Function, Function)
  UseID
  [addSaveMethod, UseID]
  [addSaveMethod, Name]
  [addSaveMethod, Namespace]
Headline
  register a method for serializing a type to MRDI format
Usage
  addSaveMethod T
  addSaveMethod(T, dataFunc)
  addSaveMethod(T, paramsFunc, dataFunc)
Inputs
  T:Type
    the Macaulay2 type to be serialized
  dataFunc:Function
    a function that takes an object of type @TT "T"@ and
    returns the data to be stored in the @TT "data"@ field
    of the MRDI JSON
  paramsFunc:Function
    a function that takes an object of type @TT "T"@ and
    returns the parameter object (e.g., the coefficient ring
    of a polynomial ring), which will itself be serialized
    recursively
  UseID => Boolean
    if @TT "true"@, objects of this type are assigned UUIDs
    so they can be referenced rather than duplicated
  Name => Function
    a function (or string) that determines the type name string
    for the @TT "_type"@ field.  By default, the @TO class@ of
    each object (as a string) is used.
  Namespace => String
    the namespace to register this save method under
Description
  Text
    This function registers a serialization method for the given type so
    that @TO saveMRDI@ knows how to convert objects of that
    type into MRDI JSON format.

    The zero-argument form @TT "addSaveMethod T"@
    is for types with no data and no parameters (the MRDI
    output will contain only a @TT "_type"@ field).

    The one-argument form @TT "addSaveMethod(T, dataFunc)"@
    is for basic (non-parametric) types whose MRDI
    representation needs only a @TT "_type"@ name and
    @TT "data"@.  The @TT "dataFunc"@ receives the object and
    should return the data portion.

    The two-argument form @TT "addSaveMethod(T, paramsFunc, dataFunc)"@
    is for parametric types.  The @TT "paramsFunc"@ returns an
    object representing the type's parameter (which will be
    recursively serialized into the @TT "_type.params"@ field),
    and @TT "dataFunc"@ returns the data.

    The @TO UseID@ option causes objects of this type to be
    assigned RFC 9562 version 4 UUIDs upon serialization.
    This is important for types like polynomial rings
    that may be shared by many objects: the ring is stored
    once in the @TT "_refs"@ section and referenced by UUID
    elsewhere.

    The @TO Namespace@ option allows registering save methods
    for different namespaces.  This is how OSCAR serialization
    support is implemented alongside Macaulay2's own namespace.

    Here we register a save method for a custom namespace.
  Example
    addNamespace("MySystem", "https://example.com", "1.0")
    addSaveMethod(ZZ, identity, Name => "MyInt", Namespace => "MySystem")
    saveMRDI(42, Namespace => "MySystem")
SeeAlso
  saveMRDI
///

doc ///
Key
  addLoadMethod
  (addLoadMethod, String, Function)
  (addLoadMethod, List, Function)
  [addLoadMethod, Namespace]
Headline
  register a method for deserializing a type from MRDI format
Usage
  addLoadMethod(typeName, f)
Inputs
  typeName:{String, List}
    the type name as it appears in the @TT "_type"@ field
    of the MRDI JSON, or a list of strings to add multiple
    load methods at the same time
  f:Function
    a function @TT "(params, data) -> Thing"@ that
    reconstructs the object
  Namespace => String
    the namespace to register this method under
Description
  Text
    This method registers a deserialization method so that @TO loadMRDI@
    knows how to reconstruct objects of a given type within a
    given namespace.

    The namespace allows the same file format to be used across
    different computer algebra systems.  The Macaulay2 namespace
    is @TT "\"Macaulay2\""@ and the OSCAR namespace is
    @TT "\"Oscar\""@.  Each namespace maintains its own type
    registry.  Use @TO addNamespace@ to register a new namespace
    before adding load methods to it.

    The loading function @VAR "f"@ receives two
    arguments:

    @UL {
	LI {TT "type", ": UPDATE ME"},
	LI {TT "data", ":  The contents of the ", TT "data", " field from the ",
	    "JSON, recursively deserialized."}}@

    The @TO List@ form allows registering the same function for
    multiple type names at once, which is useful when systems
    use different names for equivalent types.
  Text
    Here we register a load method for a custom namespace.
  Example
    addNamespace("MySystem", "https://example.com", "1.0")
    addLoadMethod("MyInt",
        (params, data) -> value data,
        Namespace => "MySystem")
    loadMRDI "{\"_ns\":{\"MySystem\":[\"https://example.com\",\"1.0\"]},\"_type\":\"MyInt\",\"data\":\"42\"}"
SeeAlso
  loadMRDI
///

doc ///
Key
  addNamespace
  (addNamespace, String, String, String)
Headline
  register a namespace for MRDI serialization
Usage
  addNamespace(ns, url, ver)
Inputs
  ns:String -- the namespace identifier
  url:String -- the URL associated with the namespace
  ver:String -- the version string for the namespace
Description
  Text
    This method registers a new namespace for use with @TO saveMRDI@ and
    @TO loadMRDI@.  A namespace must be registered before any save or load methods
    can be added to it using @TO addSaveMethod@ or @TO addLoadMethod@.

    The namespace, URL, and version are written into the
    @TT "_ns"@ field of the MRDI JSON output.

    The @TT "\"Macaulay2\""@ and @TT "\"Oscar\""@ namespaces
    are registered automatically when the package is loaded.
  Example
    addNamespace("MySystem", "https://example.com", "1.0")
    addLoadMethod("MyInt",
        (params, data) -> value data,
        Namespace => "MySystem")
    loadMRDI "{\"_ns\":{\"MySystem\":[\"https://example.com\",\"1.0\"]},\"_type\":\"MyInt\",\"data\":\"42\"}"
///

doc ///
Key
  validateMRDI
  (validateMRDI, Thing)
  (validateMRDI, String)
  (validateMRDI, HashTable)
Headline
  validate an MRDI JSON object against the format specification
Usage
  validateMRDI s
Inputs
  s:{String, HashTable}
    a JSON string or parsed JSON hash table to validate
Description
  Text
    Validates that a JSON string or hash table conforms to the
    @HREF("https://www.oscar-system.org/schemas/mrdi.json",
	"MRDI file format specification")@.
    This checks structural requirements such as:

    @UL {
	LI {"the presence of a ", TT "_type", " key"},
	LI {"that ", TT "_type", " is a string or an object with string-valued ", TT "name"},
	LI {"that ", TT "_ns", " and ", TT "_refs", " are objects (if present)"},
	LI {"that referenced objects are themselves valid MRDI"}}@

    The function produces an error if validation fails and returns
    @TO null@ on success.
  Example
    s = saveMRDI 5
    validateMRDI s
///

doc ///
Key
  Namespace
Headline
  option specifying the namespace for MRDI serialization
Description
  Text
    A symbol used as an option to @TO addSaveMethod@,
    @TO addLoadMethod@, and @TO saveMRDI@ to specify which
    namespace to use.

    Different namespaces allow the same MRDI file format to
    represent objects from different computer algebra systems.
    The @TT "\"Macaulay2\""@ and @TT "\"Oscar\""@ namespaces
    are built in.  Custom namespaces can be registered with
    @TO addNamespace@.

    When passed to @TO saveMRDI@, this determines which set of
    save methods is used and what appears in the @TT "_ns"@ field
    of the JSON output.

    When passed to @TO addSaveMethod@ or @TO addLoadMethod@, this
    determines which namespace the method is registered under.
  Text
    The same object can be serialized under different namespaces.
  Example
    saveMRDI 5
    saveMRDI(5, Namespace => "Oscar")
Subnodes
  addNamespace
///


-----------
-- tests --
-----------

TEST ///
-- loadMRDI saveMRDI x should return x
checkMRDI = x -> (
    assert BinaryOperation(symbol ===, loadMRDI saveMRDI x, x);
    -- check FileName option
    fn := temporaryFileName() | ".mrdi";
    saveMRDI(x, FileName => fn);
    assert BinaryOperation(symbol ===, loadMRDI get fn, x);
    removeFile fn;
    -- check ToString option
    h := saveMRDI(x, ToString => false);
    assert instance(h, HashTable);
    assert BinaryOperation(symbol ===, loadMRDI h, x))
checkMRDI true
checkMRDI 5
checkMRDI 5_(ZZ/7)
checkMRDI 5_(GF 7)
checkMRDI "foo"
checkMRDI ZZ
checkMRDI QQ
checkMRDI(ZZ/101)
checkMRDI GF(2, 3)
checkMRDI (a + 1)
checkMRDI(QQ[x])
checkMRDI(QQ[x][y][z])
R = QQ[x,y,z,w]
I = monomialCurveIdeal(R, {1, 2, 3})
checkMRDI I_0
checkMRDI I
checkMRDI gens I
-- rational coefficients
checkMRDI((1/2)*x + (3/4)*y - 7/3)
checkMRDI ideal((1/2)*x^2 - (3/5)*y, (7/11)*x*y + 1)
checkMRDI matrix {{(1/2)*x, (3/4)*y}, {(5/6)*x*y, (7/8)*x^2}}
-- identity elements
checkMRDI 1_R
checkMRDI id_(R^3)
-- zero elements
checkMRDI 0_R
checkMRDI ideal 0_R
checkMRDI map(R^2, R^3, 0)
-- lists
checkMRDI {true, false}
checkMRDI {1, 2, 3}
checkMRDI {x^2, y}
checkMRDI {{1, 2}, {3}}
checkMRDI {}
checkMRDI {ZZ, QQ}
checkMRDI {1, x^2, QQ}
checkMRDI {GF(2,3)}
checkMRDI {R, R}
checkMRDI {R, x^2}
checkMRDI set {1, 2, 3}
-- matrices
checkMRDI matrix {{1, 2}, {3, 4}}
checkMRDI matrix {{1/2, 3/4}, {5/6, 7/8}}
///

-* code to generate strings for the next test:

printWidth = 0
getFormattedMRDI = x -> (
    format replace(regexQuote version#"VERSION", "@VERSION@", saveMRDI x))
scan({
        true,
        5,
        5_(ZZ/7),
        5_(GF 7),
        "foo",
        ZZ,
        QQ,
        ZZ/101,
        GF(2, 3),
        a + 1,
        QQ[x],
        QQ[x][y][z],
        (R = QQ[x,y,z,w]; I = monomialCurveIdeal(R, {1, 2, 3}); I_0),
        I,
        gens I,
        {true, false},
        set {1, 2, 3}
        }, x -> << "checkMRDI " << getFormattedMRDI x << endl)

*-

TEST ///
-- saveMRDI loadMRDI x should return x (possibly up to reordering of elements)
needsPackage "JSON"
checkMRDI = x -> (
    x = replace("@VERSION@", version#"VERSION", x);
    y := saveMRDI loadMRDI x;
    assert BinaryOperation(symbol ===, fromJSON x, fromJSON y))
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"Boolean\", \"data\": true}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"ZZ\", \"data\": \"5\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": {\"params\": {\"_type\": \"QuotientRing\", \"data\": \"7\"}, \"name\": \"RingElement\"}, \"data\": \"-2\"}"
checkMRDI "{\"_type\": {\"params\": \"aadb5efe-8527-4625-be6c-57639489d0f5\", \"name\": \"GaloisField\"}, \"data\": [[[\"3\"], \"1\"], [[\"1\"], \"1\"], [[\"0\"], \"1\"]], \"id\": \"3cadb043-2df7-4057-8ec5-b3b20b3d6433\", \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"aadb5efe-8527-4625-be6c-57639489d0f5\": {\"_type\": {\"params\": {\"_type\": \"QuotientRing\", \"data\": \"2\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"a\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"3cadb043-2df7-4057-8ec5-b3b20b3d6433\", \"name\": \"RingElement\"}, \"data\": [[[\"1\"], \"1\"], [[\"0\"], \"1\"]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"3cadb043-2df7-4057-8ec5-b3b20b3d6433\": {\"_type\": {\"params\": \"aadb5efe-8527-4625-be6c-57639489d0f5\", \"name\": \"GaloisField\"}, \"data\": [[[\"3\"], \"1\"], [[\"1\"], \"1\"], [[\"0\"], \"1\"]]}, \"aadb5efe-8527-4625-be6c-57639489d0f5\": {\"_type\": {\"params\": {\"_type\": \"QuotientRing\", \"data\": \"2\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"a\"]}}}}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"String\", \"data\": \"foo\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"Ring\", \"data\": \"ZZ\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"Ring\", \"data\": \"QQ\"}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": \"QuotientRing\", \"data\": \"101\"}"
checkMRDI "{\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\"]}, \"id\": \"31292984-9503-4034-9a78-7badbc3d5710\", \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}}"
checkMRDI "{\"_type\": {\"params\": \"8731803f-89bd-4ff7-a599-79375b33cf4c\", \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"z\"]}, \"id\": \"27447205-6c41-4ed5-91ba-f7b96c0a65ce\", \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"8731803f-89bd-4ff7-a599-79375b33cf4c\": {\"_type\": {\"params\": \"81e005bb-a348-423a-a627-e96ff29a3597\", \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"y\"]}}, \"81e005bb-a348-423a-a627-e96ff29a3597\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\", \"name\": \"RingElement\"}, \"data\": [[[\"0\", \"0\", \"2\", \"0\"], [\"1\", \"1\"]], [[\"0\", \"1\", \"0\", \"1\"], [\"-1\", \"1\"]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\", \"name\": \"Ideal\"}, \"data\": [[[[\"0\", \"0\", \"2\", \"0\"], [\"1\", \"1\"]], [[\"0\", \"1\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"1\", \"1\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"2\", \"0\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"1\", \"0\"], [\"-1\", \"1\"]]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_type\": {\"params\": \"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\", \"name\": \"Matrix\"}, \"data\": [[[[[\"0\", \"0\", \"2\", \"0\"], [\"1\", \"1\"]], [[\"0\", \"1\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"1\", \"1\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"0\", \"1\"], [\"-1\", \"1\"]]], [[[\"0\", \"2\", \"0\", \"0\"], [\"1\", \"1\"]], [[\"1\", \"0\", \"1\", \"0\"], [\"-1\", \"1\"]]]]], \"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_refs\": {\"cfaa114f-9d5a-44e1-abbb-a0ee2ca94fe4\": {\"_type\": {\"params\": {\"_type\": \"Ring\", \"data\": \"QQ\"}, \"name\": \"PolynomialRing\"}, \"data\": {\"variables\": [\"x\", \"y\", \"z\", \"w\"]}}}}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": {\"params\": [\"Boolean\", \"Boolean\"], \"name\": \"List\"}, \"data\": [true, false]}"
checkMRDI "{\"_ns\": {\"Macaulay2\": [\"https://macaulay2.com\", \"@VERSION@\"]}, \"_type\": {\"params\": [\"ZZ\", \"ZZ\", \"ZZ\"], \"name\": \"Set\"}, \"data\": [\"1\", \"2\", \"3\"]}"
///

TEST ///
-- save/load Oscar objects
checkMRDI = x -> assert BinaryOperation(symbol ===,
    loadMRDI saveMRDI(x, Namespace => "Oscar"), x)
checkMRDI true
checkMRDI "foo"
checkMRDI ZZ
checkMRDI QQ
checkMRDI 5
checkMRDI(1/2)
R = ZZ[x,y,z,w]
checkMRDI R
checkMRDI random(3, R)
checkMRDI {1, "some text", true}
checkMRDI hashTable {("a", 1), ("b", 2)}
checkMRDI hashTable {("x", x)}
checkMRDI set {1, 2, 3}
checkMRDI set {x, x^2}
checkMRDI matrix(QQ, {{12, 31, 24, 78}, {51, 63, 17, 35}, {23, 99, 19, 34}})

-- objects we can load but can't save
checkLoad = (x, mrdi) -> assert BinaryOperation(symbol ===, x, loadMRDI mrdi)

-- Julia ints (we save to Oscar's ZZRingElem)
-- save(stdout, 5)
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Base.Int","data":"5"}////)
-- save(stdout, Int8(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Int8","data":"5"}////)
-- save(stdout, UInt8(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"UInt8","data":"5"}////)
-- save(stdout, Int16(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Int16","data":"5"}////)
-- save(stdout, UInt16(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"UInt16","data":"5"}////)
-- save(stdout, Int32(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Int32","data":"5"}////)
-- save(stdout, UInt32(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"UInt32","data":"5"}////)
-- save(stdout, Int64(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Base.Int","data":"5"}////)
-- save(stdout, UInt64(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"UInt64","data":"5"}////)
-- save(stdout, Int128(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Int128","data":"5"}////)
-- save(stdout, UInt128(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"UInt128","data":"5"}////)
-- save(stdout, BigInt(5))
checkLoad(5, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"BigInt","data":"5"}////)

-- Julia floating-point types
-- save(stdout, Float16(5))
checkLoad(5.0, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Float16","data":"5.0"}////)
-- save(stdout, Float32(5))
checkLoad(5.0, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Float32","data":"5.0"}////)
-- save(stdout, Float64(5))
checkLoad(5.0, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Float64","data":"5.0"}////)

-- save(stdout, Int[1, 2, 3, 4])
checkLoad({1, 2, 3, 4}, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":{"name":"Vector","params":"Base.Int"},"data":["1","2","3","4"]}////)

-- save(stdout, [1 2; 3 4])
checkLoad(matrix {{1, 2}, {3, 4}}, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":{"name":"Matrix","params":"Base.Int"},"data":[["1","2"],["3","4"]]}////)

-- https://oscar-system.github.io/rosetta-stone-db_prototype/rosetta/containers/dict-string-int.html
checkLoad(hashTable {("a", 1), ("b", 2)}, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.0.5"]},"_type":{"params":{"a":"Base.Int","b":"Base.Int","key_type":"String"},"name":"Dict"},"data":{"a":"1","b":"2"}}////)
checkLoad(hashTable {("a", 1), ("b", 2)}, ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.3.1"]},"_type":{"params":{"value_type":"Base.Int","key_type":"String"},"name":"Dict"},"data":{"a":"1","b":"2"}}////)

checkLoad("hello", "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.6.0\"]},\"_type\":\"String\",\"data\":\"hello\"}")
checkLoad(3.14, "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.6.0\"]},\"_type\":\"Float64\",\"data\":\"3.14\"}")
checkLoad(ZZ/101, "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.6.0\"]},\"_type\":\"FiniteField\",\"data\":\"101\"}")
checkLoad(3/4, "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.6.0\"]},\"_type\":{\"name\":\"QQFieldElem\",\"params\":{\"_type\":\"QQField\"}},\"data\":\"3//4\"}")
checkLoad(7_QQ, "{\"_ns\":{\"Oscar\":[\"https://github.com/oscar-system/Oscar.jl\",\"1.6.0\"]},\"_type\":{\"name\":\"QQFieldElem\",\"params\":{\"_type\":\"QQField\"}},\"data\":\"7\"}")
///

TEST ///
-- Oscar round-trip: MRDI -> M2 object -> MRDI
needsPackage "JSON"
checkMRDI = x -> (
    y := saveMRDI(loadMRDI x, Namespace => "Oscar");
    assert BinaryOperation(symbol ===, fromJSON x, fromJSON y))
-- save(stdout, true)
checkMRDI ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"Bool","data":true}////
-- save(stdout, "foo")
checkMRDI ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":"String","data":"foo"}////
-- save(stdout, (ZZRingElem(1), "some text", true))
checkMRDI ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":{"name":"Tuple","params":[{"name":"ZZRingElem","params":{"_type":"ZZRing"}},"String","Bool"]},"data":["1","some text",true]}////
-- save(stdout, Dict{String, ZZRingElem}("a" => 1, "b" => 2))
checkMRDI ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":{"name":"Dict","params":{"key_params":"String","value_params":{"name":"ZZRingElem","params":{"_type":"ZZRing"}}}},"data":{"b":"2","a":"1"}}////
-- save(stdout, matrix(QQ,[12 31 24 78; 51 63 17 35; 23 99 19 34]))
checkMRDI ////{"_ns":{"Oscar":["https://github.com/oscar-system/Oscar.jl","1.8.2"]},"_type":{"name":"MatElem","params":"3937a972-2e05-49dd-b868-94261a83c5ec"},"data":[["12","31","24","78"],["51","63","17","35"],["23","99","19","34"]],"_refs":{"3937a972-2e05-49dd-b868-94261a83c5ec":{"_type":{"name":"MatSpace","params":{"_type":"QQField"}},"data":{"ncols":"4","nrows":"3"}}}}////
///

TEST ///
-- save/load errors
checkError = (f, msg) -> (
    (ret, err) := trap f();
    assert Equation(msg, toString err))
checkError(
    () -> saveMRDI(5, Namespace => "NonExistent"),
    "unknown namespace: NonExistent")
checkError(
    () -> loadMRDI "{\"_ns\":{\"UnknownSystem\":[\"https://example.com\",\"1.0\"]},\"_type\":\"ZZ\",\"data\":\"5\"}",
    "unknown namespace: UnknownSystem")
checkError(
    () -> loadMRDI "{\"_ns\":{\"Macaulay2\":[\"https://macaulay2.com\",\"1.0\"]},\"_type\":\"NoSuchType\",\"data\":\"5\"}",
    "unknown type: NoSuchType")
///

TEST ///
-- custom namespace
addNamespace("TestSystem", "https://example.com/test", "0.1")
addSaveMethod(ZZ, identity, Name => "TestInt", Namespace => "TestSystem")
addLoadMethod("TestInt", (params, data) -> value data, Namespace => "TestSystem")
s = saveMRDI(99, Namespace => "TestSystem")
validateMRDI s
assert Equation(99, loadMRDI s)
needsPackage "JSON"
h = fromJSON s
assert(h#"_ns"#?"TestSystem")
///


TEST ///
-- validation
-- everything we generate should be valid MRDI, whether we generate a
-- string or a hash table
checkMRDI = x -> (
    validateMRDI saveMRDI x;
    validateMRDI saveMRDI(x, ToString => false))
checkMRDI true
checkMRDI 5
checkMRDI 5_(ZZ/7)
checkMRDI 5_(GF 7)
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
-- rational coefficients
checkMRDI((1/2)*x + (3/4)*y - 7/3)
-- identity and zero elements, whose data contains empty arrays
checkMRDI 1_R
checkMRDI id_(R^3)
checkMRDI 0_R
checkMRDI ideal 0_R
checkMRDI map(R^2, R^3, 0)
-- lists, whose "params" may be an empty array, an array of type
-- names, or an array of type descriptors and whole MRDI objects
checkMRDI {}
checkMRDI {1, 2, 3}
checkMRDI {ZZ, QQ}
checkMRDI {{1, 2}, {3}}
checkMRDI {1, x^2, QQ}
checkMRDI {R, x^2}
checkMRDI {GF(2, 3)}
-- matrices over ZZ and QQ
checkMRDI matrix {{1, 2}, {3, 4}}
checkMRDI matrix {{1/2, 3/4}, {5/6, 7/8}}
-- the Oscar namespace
checkMRDI = x -> validateMRDI saveMRDI(x, Namespace => "Oscar")
checkMRDI ZZ
checkMRDI QQ
checkMRDI 5
checkMRDI(1/2)
R = ZZ[x,y,z,w]
checkMRDI R
checkMRDI random(3, R)
///

TEST ///
-- validation of things the schema allows but that we don't generate

-- OSCAR writes "attrs" (by default) and "meta" (with its "metadata"
-- option); neither is in the schema, but it has no
-- "additionalProperties": false, so extra keys are allowed
validateMRDI("{\"_ns\":{\"Oscar\":[\"https://oscar-system.org\"," |
    "\"1.8.0\"]},\"_type\":\"FiniteField\",\"data\":\"2\"," |
    "\"attrs\":{\"is_finite\":{\"_type\":\"Bool\",\"data\":true}}," |
    "\"meta\":{\"name\":\"F2\"}}")
-- "attrs" may appear inside "_refs" as well
validateMRDI("{\"_type\":\"T\",\"_refs\":{\"39c5ec0e-4b25-4d09-9b3b-" |
    "6ee6be2b1a6c\":{\"_type\":\"T\",\"attrs\":{}}}}")
-- when several types share a name, OSCAR adds an "_instance" key
validateMRDI("{\"_type\":{\"name\":\"FiniteField\"," |
    "\"_instance\":\"fpField\"},\"data\":\"2\"}")
-- the keys of "_refs" are constrained only by "patternProperties", so
-- non-UUID's are allowed (their values must still be valid MRDI)
validateMRDI("{\"_type\":\"T\",\"_refs\":{\"foo\":{\"_type\":\"T\"}}}")
-- "_ns" is not required
validateMRDI "{\"_type\":\"T\",\"data\":\"5\"}"
-- booleans and nulls are valid data
validateMRDI("{\"_type\":\"T\",\"data\":[true,null,\"5\"," |
    "{\"foo\":[false]}]}")
-- the schema's "patternProperties" for the keys of a data object,
-- "^[a-zA-Z0-9_]*", matches every string, so keys are unconstrained
validateMRDI "{\"_type\":\"T\",\"data\":{\"not alphanumeric!\":\"5\"}}"

-- "params" is more permissive than "data": besides everything data
-- allows, it may contain type descriptors and entire MRDI objects,
-- which in turn may have their own "_ns"
validateMRDI("{\"_type\":{\"name\":\"PolynomialRing\",\"params\":" |
    "{\"_ns\":{\"Macaulay2\":[\"https://macaulay2.com\",\"1.0\"]}," |
    "\"_type\":\"Ring\",\"data\":\"QQ\"}},\"data\":{}}")
-- named params, as OSCAR writes for MPolyRing
validateMRDI("{\"_type\":{\"name\":\"MPolyRing\",\"params\":" |
    "{\"base_ring\":\"39c5ec0e-4b25-4d09-9b3b-6ee6be2b1a6c\"," |
    "\"symbols\":[\"x\"]}},\"data\":\"5\"}")
-- nested type descriptors, as OSCAR writes for Polyhedron
validateMRDI("{\"_type\":{\"name\":\"Polyhedron\",\"params\":" |
    "{\"pm_params\":{\"name\":\"Dict\",\"params\":{\"POINTED\":" |
    "\"Bool\",\"FACETS\":{\"name\":\"MatElem\",\"params\":" |
    "\"39c5ec0e-4b25-4d09-9b3b-6ee6be2b1a6c\"}}}}},\"data\":\"5\"}")
-- an object without a "name" key is still a valid map of params
validateMRDI("{\"_type\":{\"name\":\"T\",\"params\":" |
    "{\"params\":\"foo\"}},\"data\":\"5\"}")
///

TEST ///
-- validation errors
checkError = (mrdi, msg) -> (
    (ret, err) := trap validateMRDI mrdi;
    assert Equation(msg, toString err))
checkError(
    "{\"_ns\":{\"Macaulay2\":[\"https://macaulay2.com\",\"1.0\"]}}",
    "expected a '_type' key")
checkError(
    "{\"_type\":42}",
    "expected value of '_type' to be a string or object")
checkError(
    "{\"_type\":\"ZZ\",\"_ns\":\"bad\"}",
    "expected value of '_ns' to be an object")
checkError(
    "[1,2,3]",
    "expected an object, but got a(n) list")
checkError(
    "{\"_type\":{\"params\":\"foo\"}}",
    "expected '_type' to have a 'name' key")
checkError(
    "{\"_type\":{\"name\":5}}",
    "expected value of 'name' to be a string")
checkError(
    "{\"_type\":\"ZZ\",\"_refs\":{\"39c5ec0e-4b25-4d09-9b3b-" |
    "6ee6be2b1a6c\":{\"data\":\"5\"}}}",
    "expected a '_type' key")
checkError(
    "{\"_type\":\"ZZ\",\"id\":\"not-a-uuid\"}",
    "expected value of \"id\" to be a UUID")
-- data may not contain MRDI objects; they belong in "_refs"
checkError(
    "{\"_type\":\"ZZ\",\"data\":{\"foo\":{\"_ns\":{}}}}",
    "data cannot have a '_ns' key")
checkError(
    "{\"_type\":\"ZZ\",\"data\":{\"foo\":{\"_type\":\"ZZ\"}}}",
    "data cannot have a '_type' key")
-- integers must be serialized as strings
checkError(
    "{\"_type\":\"ZZ\",\"data\":[\"1\",[2]]}",
    "invalid data: 2")
checkError(
    "{\"_type\":{\"name\":\"T\",\"params\":5}}",
    "invalid data: 5")
-- JSON objects must have string keys
checkError(
    hashTable {(1, "ZZ")},
    "expected all keys to be strings, but got 1")
///

-- Save-path error: only ZZ, QQ, and finite prime fields are currently
-- supported as base rings. Pin the documented "not implemented yet"
-- behavior for a non-finite-prime-field quotient (audit notes:
-- MRDI.m2:188 and :193).
TEST ///
R := QQ[x];
Q := R / ideal(x^2);
-- Quotient of QQ[x] by a non-zero-dimensional polynomial ideal: not a
-- finite prime field.
assert(try (saveMRDI Q; false) else true);
-- For a more direct test we hit the QuotientRing dispatch on a quotient
-- that is *not* isFinitePrimeField.
S := QQ[y];
Q2 := S / ideal(y^3 - 1);
assert(try (saveMRDI Q2; false) else true);
-- And the same default Ring dispatch: anything that is not ZZ/QQ that
-- somehow reaches the Ring save method also errors.
T := frac(QQ[t]);
assert(try (saveMRDI T; false) else true);
///

-----------------------------------------------------------------------------
-- TODO: what's still missing
-----------------------------------------------------------------------------
-- Everything below was checked against this file on 2026-09-08.  "errors"
-- means saveMRDI/loadMRDI raises; "silent" means it round-trips without
-- complaint but loses information.
--
-- A caveat that applies throughout: in a single session,
-- loadMRDI saveMRDI x often returns the *identical* object out of the uuid
-- ref cache without ever calling the load method, so the TEST blocks above
-- cannot see any of the silent losses listed here.  They only show up when
-- the JSON is written in one process and read in another.  Any test for the
-- items below should save to a file in one M2 and load it in a second one.
--
-- == Rings ==
--
-- * Quotient rings other than ZZ/p.  addSaveMethod(QuotientRing, ...) errors
--   with "not implemented yet" unless isFinitePrimeField, and
--   loadRingElement QuotientRing has a notImplemented() branch for the same
--   case.  The machinery already exists: the GaloisField methods serialize
--   GF(p^n) as (ambient poly ring by reference, defining polynomial), which
--   is exactly what a general R/I needs, only with a list of generators
--   instead of one.  Oscar calls these MPolyQuoRing/MPolyQuoRingElem.
--
-- * ZZ/n for composite n.  Same dispatch as above, so it errors.  Oscar has
--   zzModRing/zzModRingElem.
--
-- * Fraction fields.  frac(QQ[x]) and its elements both error.  Params would
--   be the base ring, data the pair {numerator, denominator} (compare the
--   existing QQ method).  Oscar: FracField/FracFieldElem.  Note QQ is
--   already special-cased and would stay that way.  PR #4680 adds
--   ambient FractionField (and ambient LocalRing), which is exactly the
--   accessor the params function wants -- ambient frac R is R -- so this
--   gets tidier once that lands.
--
-- * Inexact fields: RealField (RR_prec), ComplexField (CC_prec), RRi, CCi,
--   and the RingFamily/InexactFieldFamily objects RR and CC themselves.  All
--   error, as do the numbers 3.5 and 1+2*ii.  Precision has to go in params,
--   and the mantissa should be written in a form that doesn't round-trip
--   through decimal -- see how Oscar serializes ArbField.  We can already
--   *load* Float64 (from Oscar), so this is asymmetric today.
--
-- * Monoid/GeneralOrderedMonoid and MonoidElement.  Needed on their own, and
--   also as the natural place to put the polynomial ring options below.
--
-- == Modules and maps ==
--
-- * Module.  Errors in the Macaulay2 namespace entirely.  In the Oscar
--   namespace there is a Module method, but only for Hom(F, G) with F and G
--   free, since it exists to serve MatSpace.  We need at least
--     - free modules with their degrees: R^{-1,-2} is not R^2;
--     - subquotients: coker, image, subquotient(gens, relations).
--   Oscar: FreeModule/SubquoModule.
--
-- * Vector.  Errors.
--
-- * Matrix is the one that worries me most, because it fails silently.  The
--   save method records only ring and entries, so source and target degrees
--   are dropped and both are assumed free:
--     R = QQ[x,y,z]; M = vars R ** R^{-3}
--     degrees source M                        -- {{4}, {4}, {4}}
--     degrees source loadMRDI saveMRDI M      -- {{1}, {1}, {1}} (new session)
--     degrees target loadMRDI saveMRDI M      -- {{0}} rather than {{3}}
--   A graded matrix comes back ungraded, so anything downstream that depends
--   on degrees (resolutions, Hilbert functions, isHomogeneous) is wrong
--   without any error being raised.  The fix is to make the params the
--   source and target modules rather than the ring, which depends on Module
--   support above.  Matrices between non-free modules are also unsupported.
--
-- * The apparent chicken and egg.  A matrix's params want to be its source
--   and target modules, but a subquotient module's data wants to be its
--   generator and relation matrices.  This looks circular and isn't, because
--   the two recursions don't meet: in M2 a module's generators and relations
--   are always maps of *free* modules, so the descent is
--
--     Matrix (general)  ->  source/target Module
--     Module (subquot)  ->  generators, relations : free -> free
--     Matrix (free)     ->  free source/target + entry table
--     Module (free)     ->  rank + degrees + Ring
--     Ring              ->  (already supported)
--
--   and it bottoms out after two steps.  I checked that the free-target
--   claim survives the constructions that look like they might break it --
--   image of a map out of a subquotient, image of a map into a subquotient,
--   ker of such a map, subquotient of a subquotient, Hom(M,N), M ** N,
--   prune -- and in every case
--     isFreeModule ambient X, isFreeModule cover X,
--     isFreeModule source X.generators, isFreeModule target X.generators,
--     isFreeModule source X.relations,  isFreeModule target X.relations
--   are all true.  M2 normalizes on construction: ambient is free by
--   definition, so there is no such thing as a subquotient whose generators
--   land in another subquotient.
--
--   So the two methods can be written in the obvious mutually recursive way,
--   with no cycle-breaking machinery:
--
--     addSaveMethod(Module,     -- free case: params = ring, data = degrees
--                               -- subquotient: params = ambient (a free
--                               -- module, by uuid), data = the generator
--                               -- and relation matrices
--                   UseID => true)
--     addSaveMethod(Matrix, f -> {target f, source f}, f -> entries f)
--
--   The free module is the base case that stops the descent, and giving
--   Module UseID => true means a source and target shared between several
--   matrices are emitted once into _refs.
--
--   Two things to get right on the load side:
--
--     - map(target f, source f, entries f) reconstructs a matrix equal to
--       the original, including when source and target are subquotients
--       (entries f is the cover-level table, and map takes it in those same
--       terms), and R^(-degrees F) reconstructs a free module identical to
--       F.  So the round trip really is just those three pieces...
--     - ...except for Degree, which is a fourth piece and is *not* implied
--       by the other three:
--         h = map(R^1, R^1, {{x}}, Degree => {1})
--         degree h                                     -- {1}
--         degree map(target h, source h, entries h)    -- {0}
--       so the matrix's Degree has to be stored alongside the entries.
--
--   Worth knowing, though, that the DAG property above is load-bearing
--   rather than merely convenient.  maybeUuid does
--       refs#i ??= toMRDI(ns, x, refs)
--   which recurses to completion *before* it stores anything under refs#i,
--   so the ref table can't break a cycle -- a genuinely self-referential
--   object would recurse until the stack ran out rather than emitting a
--   uuid back-reference.  If we ever do serialize something cyclic (a
--   MutableHashTable holding itself, say), the fix is one line: put a
--   placeholder in refs#i first, then recurse and overwrite it.  For
--   modules and matrices we don't need it.
--
-- * RingMap.  Errors.  Params would be (source, target), data the images of
--   the generators; DegreeMap/DegreeLift would need to come along too.
--
-- * MutableMatrix.  Errors.
--
-- * GroebnerBasis and Resolution are Core types but are engine handles; they
--   are probably not worth serializing directly.  Complexes lives in a
--   package now, not Core, so it's out of scope here.
--
-- == Ideals ==
--
-- * Ideal itself is fine over the coefficient rings we support, and it
--   inherits down to MonomialIdeal on the save side -- but there is no
--   load method registered for "MonomialIdeal", so
--     loadMRDI saveMRDI monomialIdeal(x, y)
--   fails with "unknown type: MonomialIdeal".  Either register the type or
--   have the save method emit "Ideal".  This asymmetry is worth auditing for
--   in general: any subclass of a type with a save method inherits it and
--   gets a _type name with no matching load method.
--
-- == Basic and container types (Macaulay2 namespace) ==
--
-- Only List and Set are handled.  Still missing, all erroring:
--
-- * Sequence and Array (and VisibleList generally).  The List methods would
--   almost work as is; they mainly need distinct type names so the class is
--   restored rather than flattened to List.
-- * HashTable and MutableHashTable.  The Oscar namespace has Dict, but it
--   requires homogeneous keys and values, which M2 hash tables don't have to
--   be; the Macaulay2 namespace should allow heterogeneous ones.
-- * Option and OptionTable.
-- * Tally and VirtualTally -- the multiset generalization of the Set support
--   that's already here.
-- * Symbol and IndexedVariable.  Needed in their own right, but also for the
--   Variables census item below.
-- * Nothing, i.e. null.
-- * InfiniteNumber (infinity), IndeterminateNumber, and Constant (pi, ii,
--   EulerConstant).
-- * Partition.
-- * BettiTally, MultigradedBettiTally, ProjectiveHilbertPolynomial.
-- * Net.
--
-----------------------------------------------------------------------------
-- TODO: census of polynomial ring options
-----------------------------------------------------------------------------
-- addSaveMethod(PolynomialRing, ...) stores exactly
--     {"variables" => toString \ gens R}
-- with the coefficient ring as params, and the load method is
--     params.Type[Variables => data#"variables"]
-- so every monoid option other than Variables is currently dropped, and
-- dropped silently -- the ring that comes back is a valid ring, just not the
-- one that was saved.  These two records are the complete serializations of
--     QQ[x, y, Degrees => {2, 3}, MonomialOrder => Lex]
--     QQ[x, y]
-- and they differ only in the uuid.
--
-- But "everything in monoidDefaults" is the wrong target to aim at, because
-- monoidDefaults is the *input* language and a good deal of it is absorbed
-- into other options at construction time.  M2's own answer to "how do you
-- rebuild a ring from its options" is newRing (newring.m2:31):
--
--     (coefficientRing R)(monoid [merge(options R, ..., last)])
--
-- i.e. feed `options R` -- the normalized table, not the user's input --
-- back to monoid.  So the real question is which keys survive into
-- `options R`, and which of those are recoverable from the others.
--
-- == Absorbed at construction: do NOT serialize ==
--
-- Three of the eighteen entries in monoidDefaults are not keys of
-- `options R` at all.  Serializing them separately would at best be
-- redundant and at worst double-apply:
--
-- Weights           Folded into MonomialOrder as a leading Weights block:
--                     options (QQ[x, y, Weights => {3, 5}])
--                     -- MonomialOrder => {Weights => {3,5}, MonomialSize =>
--                     --                   32, GRevLex => {1,1}, Position => Up}
--                     -- and no Weights key at all
-- MonomialSize      Likewise folded in, as a MonomialSize block inside
--                   MonomialOrder.  Passing it again alongside a saved
--                   MonomialOrder yields {MonomialSize => 32,
--                   MonomialSize => 8, ...} -- harmless but wrong-looking.
-- VariableBaseName  Consumed.  It only generates names when Variables is
--                   given as a number; once the names exist it's gone.
--
-- == Derived from other options: serialize only the exceptions ==
--
-- DegreeRank        = #(first Degrees).  The one case it isn't is a ring
--                   with no variables, where Degrees is {} -- and
--                   QQ[Variables => 0, DegreeRank => 3] is legal.  It's one
--                   integer, so just store it.
-- DegreeGroup       = ZZ^DegreeRank whenever it's free, which is almost
--                   always; monoids.m2's own isDefault uses exactly
--                   `isFreeModule opts#DegreeGroup` as the "not worth
--                   printing" test.  Only torsion grading groups need
--                   storing, and then the value is a Module (e.g.
--                   `cokernel matrix {{0}, {2}}`), so this one waits on
--                   Module support.  M2 warns that such rings are
--                   experimental, so it's a fair thing to defer.
-- Local             Its entire effect is already visible elsewhere: it sets
--                   Global => false and prepends Weights => {-1, ...} to
--                   MonomialOrder.  Re-passing Local => true on top of an
--                   already-normalized MonomialOrder appends a *second*
--                   copy of that weight block, and the copies accumulate:
--                     R = QQ[x, y, Local => true]
--                     again = R -> (coefficientRing R)(monoid [options R])
--                     -- one round trip:    {Weights, MonomialSize, Weights, GRevLex, Position}
--                     -- three round trips: {Weights, MonomialSize, Weights, Weights, Weights, GRevLex, Position}
--                   I checked that the induced order is unchanged (the extra
--                   blocks are tiebreakers after an identical one), so this
--                   is bloat rather than a wrong answer -- but it means the
--                   naive "save options R, pass it back" recipe is not
--                   idempotent, and neither is newRing.  Better to save
--                   Global plus the normalized MonomialOrder and not
--                   re-pass Local.  The cost is cosmetic: (options R).Local
--                   reads false and the ring no longer prints Local => true.
-- Global            Keep it, per the above -- it's the flag that carries
--                   Local's meaning without re-triggering Local's rewrite.
--
-- == Genuinely independent: must serialize ==
--
-- Variables         PARTIAL today.  Saved as strings, and any name that
--                   isn't a valid symbol fails to load, because findSymbols
--                   calls baseName' on it.  Subscripted variables are the
--                   common casualty:
--                     E = QQ[e_1..e_3]
--                     loadMRDI saveMRDI E   -- (new session)
--                     -- error: expected strings, integers, or symbols
--                   Needs a real representation for IndexedVariable, not
--                   toString.
-- Degrees           Not currently saved; everything comes back degree 1:
--                     R = QQ[x, y, Degrees => {2, 3}]
--                     degrees loadMRDI saveMRDI R  -- {{1}, {1}} (new session)
--                   Note that it is *not* recoverable from MonomialOrder,
--                   even though the GRevLex block looks like it might carry
--                   it: for Degrees => {2, 3} the block is GRevLex => {2, 3},
--                   but for DegreeRank => 2 the degrees are {{1,0},{0,1}}
--                   while the block is still GRevLex => {1, 1}.  GRevLex
--                   stores the heft-collapsed vector, not the multidegrees.
--                   Together with the Matrix item above, this is the biggest
--                   correctness gap in the package.
-- Heft              Usually findHeft's answer given Degrees, but the user
--                   can override it with a different vector and M2 keeps
--                   what it was given:
--                     (options (QQ[x, y, Degrees => {1,2}, Heft => {3}])).Heft  -- {3}
--                     (options (QQ[x, y, Degrees => {1,2}])).Heft              -- {1}
--                   It's also null for Laurent and torsion-graded rings, so
--                   the serialization has to allow null.
-- Inverses          Not derivable, despite appearances.  It does show up in
--                   MonomialOrder (RevLex becomes GroupRevLex), but feeding
--                   that order back without Inverses => true is rejected, so
--                   the flag has to be stored in its own right.  This is
--                   also the one option whose absence errors rather than
--                   degrading silently, since the element data carries
--                   negative exponents:
--                     R = QQ[t, Inverses => true, MonomialOrder => RevLex]
--                     loadMRDI saveMRDI t^-1   -- (new session)
--                     -- error: element is not invertible in this ring
--                   Laurent rings are common enough (toric, tropical) that
--                   this belongs near the front of the queue.
-- MonomialOrder     Not saved; everything comes back GRevLex.  Serialize the
--                   *normalized* form -- the VerticalList monoids.m2 stores
--                   back into opts.MonomialOrder after makeMonomialOrdering
--                   -- rather than the user's input form.  That's a strictly
--                   smaller language: fixup1 in engine.m2 has already
--                   expanded Eliminate n, ProductOrder {...}, bare symbols
--                   and GLex into the primitives, so all we ever have to
--                   write down is
--                     Lex, RevLex, GroupLex, GroupRevLex, NCLex => n
--                     GRevLex => {weights}
--                     Weights => {...}, Position => Up|Down, MonomialSize => n
--                   plus the size-specialized spellings LexTiny/LexSmall/
--                   GRevLexTiny/GRevLexSmall that a small MonomialSize
--                   introduces.  I confirmed Eliminate, ProductOrder and
--                   Position => Down all survive a normalize-and-refeed
--                   round trip unchanged.
-- SkewCommutative   Not saved, so exterior algebras come back commutative --
--                   a silent wrong answer for every computation in them.
--                   Easy once Variables is solid: M2 normalizes it to a
--                   plain list of variable indices ({0, 1, 2}), so it's a
--                   list of integers with no name dependence.
-- WeylAlgebra       Not saved either, and the same silent-wrong-answer
--                   problem: differential operators become polynomials.
--                   Slightly more awkward than SkewCommutative because M2
--                   does *not* normalize it to indices -- (options W).
--                   WeylAlgebra is {{x, dx}}, a list of pairs of
--                   MonoidElements.  But monoid accepts index pairs on the
--                   way in (WeylAlgebra => {0 => 1} works), so save
--                   `apply(..., index)` and let it renormalize on load.
-- Join              Only observable for towers, e.g. QQ[x][y, Join => false].
--                   A three-valued flag (null/true/false); cheap to store,
--                   and the existing tower tests don't cover it.
--
-- Constants         A plain boolean, and it does survive into the option
--                   table ((options monoid[x, Constants => true]).Constants
--                   is true), so there is nothing hard about storing it.
--                   Blocked on tooling rather than design: on development as
--                   of this writing, ZZ[x, Constants => true] dies with
--                   SIGFPE and a core dump (the monoid builds fine, so it's
--                   the rawTowerRing path in the ring constructor).  That is
--                   fixed in PR #4680, so this can't be exercised until
--                   #4680 lands.  Worth confirming afterwards that the tower
--                   representation actually survives a round trip, rather
--                   than assuming the boolean is the whole story.
--
-- == Can't serialize ==
--
-- DegreeMap         A FunctionClosure, only non-null when Join => false.
-- DegreeLift        Same.  We can't write a function into JSON; the choices
--                   are to refuse to save such a ring, or restrict to the
--                   maps M2 can reconstruct on its own.
--
-- Two things that aren't monoid options but belong in the same census:
--
-- * Coefficient rings.  A polynomial ring is only as serializable as its
--   coefficient ring, so everything in the Rings section above -- general
--   quotients, fraction fields, RR/CC -- is also a hole here.  ZZ, QQ, ZZ/p,
--   GF, and towers of those all work today.
-- * The degrees of the ring's own generators as reported by degreesRing/
--   degreeLength, which follow from Degrees and DegreeGroup.
