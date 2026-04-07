stderr << version << endl
stderr << "Macaulean M2 Startup" << endl

needsPackage "JSONRPC"
needsPackage "MRDI"
needsPackage "JSON"
needsPackage "Parsing"
--get the actual parser from the JSON package so we can run it character by character
importFrom_JSON {"jsonTextP"}
--get the helper function from JSONRPC that can take already parsed JSON objects
importFrom_JSONRPC {"handleRequestHelper"}

stderr << "Packages Loaded" << endl

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
    ZZ => "Int",
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
fromLean ZZ := R -> identity

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


--read in a single JSON object from the stream
--currently this uses getc which is inefficient, but means we don't have to deal
--with buffering ourselves
--will block if there's nothing to read
--We need either this, a message oriented socket api, or something like what LSP does with Content-Length
fromJSONStream = method();
fromJSONStream File := (file) -> (
    currParser := jsonTextP;
    while true do (
        --TODO use utf8
        currParser = currParser (getc file);
        if currParser === null then error "JSON parsing failed";
        --poor man's check of whether the parser is complete, see if passing null returns a value
        parseResult := currParser null;
        if parseResult =!= null then return parseResult;
        )
    )

readLSPHeaderLine = method();
readLSPHeaderLine File := (file) -> (
    line := "";
    while not atEndOfFile file do (
        currChar := getc file;
        if currChar == "\r" then (
            if atEndOfFile file then return line | currChar;
            nextChar := getc file;
            if nextChar == "\n" then return line;
            line |= (currChar | nextChar);
            )
        else line |= currChar
        );
    line
    )

readLSPHeaders = method();
readLSPHeaders File := (file) -> (
    headers := while true list (
        headerLine := readLSPHeaderLine file;
        if headerLine=="" then break;
        headerLine);
    hashTable apply(headers, h -> (
            firstColon := first first regex("[:]",h);
            --TODO this is supposed to be case insensitive
            headerName := substring(0,firstColon, h);
            headerValue := substring(firstColon+1, h);
            (headerName, replace("\\s+$","",replace("^\\s+","",headerValue)))
            ))
    )


--main loop, reading one JSON expression at a time
--right now it uses the same file for input and output
macauleanMainLoop = method();
macauleanMainLoop (JSONRPCServer, File) := (server, file) -> (
    while true do (
        wait file;
        if atEndOfFile file then return;
        if isReady file then (
            headers := readLSPHeaders file;
            stderr << headers << endl;
            requestLength := (NNParser : charAnalyzer) headers#"Content-Length";
            requestBody := concatenate while requestLength > 0 list (
                block := read(file,requestLength);
                if length block == 0 then (
                    stderr << "Truncated Request" << endl;
                    return);
                requestLength -= length block;
                block
                );
            response := handleRequest_server requestBody;
            file << "Content-Length: " << length response << "\r\n";
            file << "\r\n";
            file << response;
            )
        )
    )

--setup the server, copied from example.m2
server = new JSONRPCServer
--server#"logger" = (str) -> (stderr << str << endl)

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
	I := ideal apply(idealmrdi, g -> (
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

registerMethod(server, "factor", (nmrdi) -> (
	n := loadMRDI nmrdi;
	saveMRDI(toList \ toList factor n)))

registerMethod(server, "testMethod", (expr) -> (
        toExternalString value expr
        ))

registerMethod(server, "factorInt", (x) -> (
        toList \ toList factor x
    )
)

registerMethod(server, "mrdiEcho", (mrdi) -> (
        f := loadMRDI mrdi;
        stderr << f << endl;
        saveMRDI(f, Namespace => "Lean")
    )
)

registerMethod(server, "mrdiFactor", (mrdi) -> (
        f := loadMRDI mrdi;
        stderr << f << endl;
        apply(toList \ toList factor f, term -> (saveMRDI(term#0, Namespace => "Lean"), term#1))
    )
)

macauleanMainLoop(server, stdio);
-- inputJSON = fromJSONStream stdio;
-- stdio << toExternalString sum inputJSON << endl;

stderr << "Macaulay2 Finished" << endl
