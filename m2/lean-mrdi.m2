needsPackage "MRDI"

addNamespace("Lean", "https://github.com/leanprover/lean4", "4.27.0")

leanRings = hashTable {
    QQ => "Rat",
    }
M2Rings = hashTable apply(pairs leanRings, (k, v) -> (v, k))

M2toLean = hashTable {
    QQ => x -> {numerator x, denominator x},
    }

LeantoM2 = hashTable {
    QQ => x -> x#0 / x#1,
    }

addSaveMethod(RingElement,
    f -> (
	coeffmap := new MutableHashTable;
	R := ring f;
	coeffRing := coefficientRing R;
	n := numgens R;
	polynomial := apply(listForm f, (mon, coeff) -> (
		coeffmap#coeff ??= first(n, n += 1);
		append(
		    apply(select(#mon, i -> mon#i != 0),
			j -> toString \ {j, mon#j}),
		    toString \ {coeffmap#coeff, 1})));
	hashTable {
	    "coefficient_ring" => leanRings#coeffRing,
	    "polynomial" => polynomial,
	    "coefficient_map" => apply(pairs coeffmap,
		(coeff, var) -> toString \ {var, M2toLean#coeffRing coeff}),
	    }),
    Name => "ConcretePoly",
    Namespace => "Lean")

addLoadMethod("ConcretePoly",
    (params, data, f) -> (
	kk := M2Rings#(data#"coefficient_ring");
	polynomial := apply(data#"polynomial", term ->
	    apply(term, pair -> value \ pair));
	coeffmap := hashTable apply(data#"coefficient_map", pair -> value \ pair);
	-- some of our variables are really coefficients; remove them
	varlist := sort \\ unique \\ first \ flatten polynomial;
	varlist -= set keys coeffmap;
	-- keep track of indices of each variable
	varmap := hashTable apply(#varlist, i -> (varlist#i, i));
	R := kk[vars varlist];
	sum(polynomial, term -> (
		product(toSequence \ term, (var, pow) ->
		    (R_(varmap#var))^pow ?? (LeantoM2#kk coeffmap#var))))
	),
    Namespace => "Lean"
    )

R = QQ[x,y]
f = 1/2*x + 1/2*y
mrdi = saveMRDI(f, Namespace => "Lean")

-- {"_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.27.0"]}, "_type": "ConcretePoly", "data": {"polynomial": [[[0, 1], [2, 1]], [[1, 1], [2, 1]]], "coefficient map": [[2, [1, 2]]], "coefficient ring": "Rat"}}

g = loadMRDI mrdi
phi = map(R, ring g, vars R)
assert Equation(phi g, f)
