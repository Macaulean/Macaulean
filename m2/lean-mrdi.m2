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
