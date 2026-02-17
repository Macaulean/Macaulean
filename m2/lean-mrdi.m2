-----------------------------------------------------
-- M2 classes to represent Lean polynomial objects --
-----------------------------------------------------

LeanGrindCommRingPoly = new SelfInitializingType of List
ConcretePoly = new SelfInitializingType of HashTable

toLean = method()
toLean ZZ := identity
toLean QQ := x -> {numerator x, denominator x}

leanRings = hashTable {
    QQ => "Rat",
    }
M2Rings = applyPairs(leanRings, reverse)

new ConcretePoly from RingElement := (T, f) -> (
	coeffmap := new MutableHashTable;
	R := ring f;
	n := numgens R;
	new T from {
	    "poly" => LeanGrindCommRingPoly apply(listForm f, (mon, coeff) -> (
		    mon = apply(positions(mon, not zero), i -> {i, mon#i});
		    if liftable(coeff, ZZ) then coeff ^= ZZ
		    else (
			mon = append(mon,
			    {coeffmap#coeff ??= first(n, n += 1), 1});
			coeff = 1);
		    {coeff, mon})),
	    "coefficients" => apply(pairs coeffmap, (a, i) -> {i, toLean a}),
	    "params" => leanRings#(coefficientRing R)})

fromLean = method(Dispatch => Type)
fromLean QQ := R -> x -> x#0 / x#1

value ConcretePoly := f -> (
    kk := M2Rings#(f#"params");
    coeffmap := hashTable f#"coefficients";
    -- some of our variables are really coefficients; remove them
    n := max \\ first \ flatten \\ last \ f#"poly";
    varlist := toList(0..n) - set keys coeffmap;
    -- keep track of indices of each variable
    varmap := hashTable apply(#varlist, i -> (varlist#i, i));
	R := kk[vars varlist];
	sum(toSequence \ f#"poly", (coeff, mon) -> (
		coeff * product(toSequence \ mon, (var, pow) ->
		    (R_(varmap#var))^pow ?? (fromLean kk) coeffmap#var))))

------------------------------------------
-- MRDI serialization & deserialization --
------------------------------------------

needsPackage "MRDI"

addNamespace("Lean", "https://github.com/leanprover/lean4", "4.26.0-rc1")

addSaveMethod(LeanGrindCommRingPoly,
    toList,
    Namespace => "Lean",
    UseID => true)

addSaveMethod(ConcretePoly,
    f -> f#"params",
    f -> hashTable {
	"poly" => f#"poly",
	"coefficients" => f#"coefficients"},
    Namespace => "Lean")

addLoadMethod("Lean.Grind.CommRing.Poly",
    (params, data) -> LeanGrindCommRingPoly apply(data, term -> {
	    value term#0,
	    apply(term#1, varpow -> value \ varpow)}),
    Namespace => "Lean")

loadCoefficient = R -> x -> (
    if R == "Rat" then {value x#0, value x#1}
    else error "unknown ring")

addLoadMethod("ConcretePoly",
    (params, data) -> ConcretePoly {
	"poly" => data#"poly",
	"coefficients" => apply(toSequence \ data#"coefficients",
	    (i, coeff) -> {value i, (loadCoefficient params) coeff}),
	"params" => params},
    Namespace => "Lean")

------------------------------------------
-- JSON-RPC method for ideal membership --
------------------------------------------

needsPackage "JSON"
needsPackage "JSONRPC"

server = new JSONRPCServer

-- input:
--   polymrdi: MRDI-serialized ConcretePoly
--   idealmrdi: list of MRDI-serialized ConcretePoly's
-- output:
--   a hash table:
--     "quotient" => list of MRDI-serialized ConcretePoly's
--     "remainder" => MRDI-serialized ConcretePoly (hopefully 0)

registerMethod(server, "quotientRemainder", (polymrdi, idealmrdi) -> (
	f := value loadMRDI polymrdi;
	R := ring f;
	I := ideal apply(fromJSON idealmrdi, g -> (
	       sub(value loadMRDI g, R)));
	(q, r) := quotientRemainder(matrix f, gens I);
	hashTable {
	    "quotient" => apply(flatten entries q,
		g -> saveMRDI(ConcretePoly g,
		    Namespace => "Lean",
		    ToString => false)),
	    "remainder" => saveMRDI(ConcretePoly r_(0,0),
		Namespace => "Lean",
		ToString => false)}))

end

-------------
-- example --
-------------

-- construct and serialize the ideal and polynomial

R = QQ[x,y,z,w]
I = monomialCurveIdeal(R, {1,2,3})
f = random(3, I)
polymrdi = saveMRDI(ConcretePoly f, Namespace => "Lean")
idealmrdi = toJSON apply(I_*, g ->
    saveMRDI(ConcretePoly g, Namespace => "Lean", ToString => false))

-- make the request

request = makeRequest("quotientRemainder", {polymrdi, idealmrdi}, 1)
response = handleRequest(server, request)

-- de-serialize and check

result = (fromJSON response)#"result"
assert zero value loadMRDI result#"remainder" -- in ideal! 🎉
certificate = apply(result#"quotient", gmrdi -> (
	g := value loadMRDI gmrdi;
	-- since we don't store the ring, they're all in different rings
	phi := map(R, ring g, vars R);
	phi g))
assert Equation(f, (matrix {certificate} * transpose gens I)_(0,0))
