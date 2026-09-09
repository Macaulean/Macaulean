newPackage(
    "Macaulean",
    Version => "0.1",
    Date => "September 2026",
    Headline => "Macaulay2 <-> Lean interface",
    Authors => {
        {Name => "Matt Ballard",
         Email => "ballard@math.sc.edu",
         HomePage => "https://www.matthewrobertballard.com/"},
        {Name => "Anton Leykin",
         Email => "leykin@math.gatech.edu",
         HomePage => "https://antonleykin.math.gatech.edu/"},
        {Name => "Mike Stillman",
         Email => "mes15@cornell.edu",
         HomePage => "https://pi.math.cornell.edu/~mike/"},
        {Name => "Damiano Testa",
         Email => "D.Testa@warwick.ac.uk",
         HomePage => "https://adomani.github.io/"},
        {Name => "Doug Torrance",
         Email => "dtorrance9@gatech.edu",
         HomePage => "https://d-torrance.github.io"},
        {Name => "Jay Yang",
         Email => "jay.k.yang@vanderbilt.edu",
         HomePage => "https://jkyang92.github.io/"}},
    Keywords => {"Interfaces"},
    PackageExports => {"JSONRPC", "MRDI"},
    PackageImports => {"Parsing"})

export {
    -- classes
    "ConcretePoly",
    "LeanGrindCommRingPoly",

    -- methods
    "macauleanServer",
    "macauleanStart"
}

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

addNamespace("Lean", "https://github.com/leanprover/lean4", "4.29.1")

addSaveMethod(RingElement,
    f -> leanRings#(coefficientRing ring f),
    f -> apply(listForm f, (m, c) -> {toLean c, m}),
    Name => "Polynomial",
    Namespace => "Lean")

-- eventually replace fromLean w/ this
fromLean2 = method(Dispatch => Type)
fromLean2 QQ := R -> x -> value x#0 / value x#1
fromLean2 ZZ := R -> value

addLoadMethod("Polynomial",
    (params, data) -> (
	if #data == 0 then return 0;
	kk := M2Rings#params;
	R := kk[vars(0..<#last first data)];
	sum(data, cm -> (fromLean2 kk) cm#0 * product(#cm#1,
		i -> R_i^(value cm#1#i)))),
    Namespace => "Lean")

addSaveMethod(LeanGrindCommRingPoly,
    toList,
    Name => "Lean.Grind.CommRing.Poly",
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
    else if R == "Int" then value x
    else error("unknown ring: ", R))

addLoadMethod("ConcretePoly",
    (params, data) -> ConcretePoly {
	"poly" => data#"poly",
	"coefficients" => apply(toSequence \ data#"coefficients",
	    (i, coeff) -> {value i, (loadCoefficient params) coeff}),
	"params" => params},
    Namespace => "Lean")


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
    echoOff file;
    while true do (
        wait file;
        if atEndOfFile file then return;
        if isReady file then (
            headers := readLSPHeaders file;
            --stderr << headers << endl;
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

---------------------
-- JSON-RPC server --
---------------------

-- a function rather than a global so that each test gets a fresh server
macauleanServer = () -> (
    server := new JSONRPCServer;
    -- setLogger(server, str -> stderr << str << endl);

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
		    g -> saveMRDI(g,
			Namespace => "Lean",
			ToString => false)),
		"remainder" => saveMRDI(r_(0,0),
		    Namespace => "Lean",
		    ToString => false)}));

    registerMethod(server, "factor", (nmrdi) -> (
	    n := loadMRDI nmrdi;
	    saveMRDI(toList \ toList factor n)));

    registerMethod(server, "testMethod", (expr) -> (
	    toExternalString value expr));

    registerMethod(server, "factorInt", (x) -> (
	    toList \ toList factor x));

    registerMethod(server, "mrdiEcho", (mrdi) -> (
	    f := loadMRDI mrdi;
	    stderr << f << endl;
	    saveMRDI(f, Namespace => "Lean")));

    registerMethod(server, "mrdiFactor", (mrdi) -> (
	    f := loadMRDI mrdi;
	    stderr << f << endl;
	    apply(toList \ toList factor f, term -> (
		    saveMRDI(term#0, Namespace => "Lean"), term#1))));

    server)

macauleanStart = () -> macauleanMainLoop(macauleanServer(), stdio);

beginDocumentation()

----------------------------------
-- ConcretePoly <-> RingElement --
----------------------------------

TEST ///
-- ConcretePoly round trips
-- MRDI would hand back the object we just saved, so make it forget the UUID's
debug MRDI
roundTrip = f -> (
    mrdi := saveMRDI(new ConcretePoly from f, Namespace => "Lean");
    scan(keys thingsByUuid, uuid -> remove(thingsByUuid, uuid));
    value loadMRDI mrdi)
-- polynomials come back in rings with (possibly) fewer variables
toR = (R, f) -> (map(R, ring f, (gens R)_{0..<numgens ring f})) f

R = QQ[x,y,z,w]
f = random(3, R)
assert Equation(f, toR(R, roundTrip f))

-- unused trailing variables aren't serialized, so numgens isn't preserved
g = roundTrip(x*z^2)
assert Equation(numgens ring g, 3) -- z is the last variable used
assert Equation(x*z^2, toR(R, g))
g = roundTrip x
assert Equation(numgens ring g, 1) -- y, z, and w are gone
assert Equation(x, toR(R, g))

-- constants and zero
assert Equation(1, roundTrip 1_R)
assert Equation(0, roundTrip 0_R)

-- coefficients that don't lift to ZZ become variables numbered past all of R
g = roundTrip(1/2*x^2 + 3*y)
assert Equation(numgens ring g, 4)
assert Equation(1/2*x^2 + 3*y, toR(R, g))

-- coefficient ring ZZ
S = ZZ[x,y]
h = x^2 + 3*y - 1
assert Equation(h, toR(S, roundTrip h))
///

TEST ///
-- how ConcretePoly represents its coefficients
R = QQ[x,y]
cp = new ConcretePoly from 1/2*x^2 + 3*y
assert Equation(cp#"params", "Rat")
-- 1/2 becomes variable 2, just past y, stored as {numerator, denominator}
assert Equation(cp#"coefficients", {{2, {1, 2}}})
assert Equation(sort toList cp#"poly",
    sort {{1, {{0, 2}, {2, 1}}}, {3, {{1, 1}}}})

S = ZZ[x,y]
cp = new ConcretePoly from x^2 + 3*y - 1
assert Equation(cp#"params", "Int")
assert Equation(cp#"coefficients", {}) -- every coefficient lifts to ZZ
///

--------------------------------
-- Polynomial <-> RingElement --
--------------------------------

TEST ///
-- RingElement round trips; no UUID's or references are involved here
R = QQ[x,y,z]
f = x*z^2 - 3/2*y
g = loadMRDI saveMRDI(f, Namespace => "Lean")
assert Equation(f, (map(R, ring g, vars R)) g)

S = ZZ[x,y,z]
h = x*z^2 - 3*y
k = loadMRDI saveMRDI(h, Namespace => "Lean")
assert Equation(h, (map(S, ring k, vars S)) k)

-- the zero polynomial carries no ring information
z0 = loadMRDI saveMRDI(0_R, Namespace => "Lean")
assert instance(z0, ZZ)
assert zero z0
///

-----------------
-- wire format --
-----------------

TEST ///
-- MRDI produced by M2 must use the type names that Lean expects
needsPackage "JSON"
R = QQ[x,y,z]
mrdi = fromJSON saveMRDI(new ConcretePoly from x + 1/2*y, Namespace => "Lean")
assert Equation(mrdi#"_type"#"name", "ConcretePoly")
assert Equation(mrdi#"_type"#"params", "Rat")
assert Equation(first keys mrdi#"_ns", "Lean")
-- the underlying Lean.Grind.CommRing.Poly is stored as a reference
assert Equation(#mrdi#"_refs", 1)
assert Equation((first values mrdi#"_refs")#"_type", "Lean.Grind.CommRing.Poly")

mrdi = fromJSON saveMRDI(x + 1/2*y, Namespace => "Lean")
assert Equation(mrdi#"_type"#"name", "Polynomial")
assert Equation(mrdi#"_type"#"params", "Rat")
///

TEST ///
-- everything we serialize must be valid MRDI
needsPackage "JSON"
lean = x -> saveMRDI(x, Namespace => "Lean", ToString => false)

R = QQ[x,y,z]
f = x*z^2 - 3/2*y
validateMRDI lean f
validateMRDI lean 0_R -- the zero polynomial
cp = new ConcretePoly from f
validateMRDI lean cp
validateMRDI lean cp#"poly" -- a bare Lean.Grind.CommRing.Poly

S = ZZ[x,y,z]
g = x*z^2 - 3*y
validateMRDI lean g
validateMRDI lean(new ConcretePoly from g)

-- and so must everything the server hands back
server = macauleanServer()
call = (m, params) -> (
    (fromJSON handleRequest(server, makeRequest(m, params, 1)))#"result")

I = ideal(x*z, y)
result = call("quotientRemainder",
    {lean(new ConcretePoly from x*z^2),
	apply(first entries gens I, h -> lean new ConcretePoly from h)})
validateMRDI result#"remainder"
scan(result#"quotient", validateMRDI)

validateMRDI call("mrdiEcho", {lean f})
scan(call("mrdiFactor", {lean(x^2 - y^2)}), term -> validateMRDI term#0)
///

TEST ///
-- MRDI produced by Lean must load in M2
-- these fixtures are pinned by #guard_msgs in MacauleanTest/Poly.lean

-- a bare Lean.Grind.CommRing.Poly
p = loadMRDI "{\"data\": [[\"3\", []], [\"5\", [[\"2\", \"3\"]]], [\"0\", []]],
 \"_type\": \"Lean.Grind.CommRing.Poly\",
 \"_ns\": {\"Lean\": [\"https://github.com/leanprover/lean4\", \"4.33.1\"]}}"
assert(class p === LeanGrindCommRingPoly)
assert Equation(toList p, {{3, {}}, {5, {{2, 3}}}, {0, {}}})

-- a ConcretePoly: 3*x_0*x_2^2 + x_0*x_1^2 + 1, where x_0 is really 1/2
f = value loadMRDI "{\"data\":
 {\"poly\": \"bf9837e6-468a-41df-a270-aea8d4a747e8\",
  \"coefficients\": [[\"0\", [\"1\", \"2\"]]]},
 \"_type\": {\"params\": \"Rat\", \"name\": \"ConcretePoly\"},
 \"_refs\":
 {\"bf9837e6-468a-41df-a270-aea8d4a747e8\":
  {\"data\":
   [[\"3\", [[\"0\", \"1\"], [\"2\", \"2\"]]],
    [\"1\", [[\"0\", \"1\"], [\"1\", \"2\"]]],
    [\"1\", []]],
   \"_type\": \"Lean.Grind.CommRing.Poly\"}},
 \"_ns\": {\"Lean\": [\"https://github.com/leanprover/lean4\", \"4.33.1\"]}}"
S = ring f
assert Equation(numgens S, 2)
assert Equation(f, 1/2*S_0^2 + 3/2*S_1^2 + 1)

-- a Polynomial
f = loadMRDI "{\"data\":
 [[[\"2\", \"1\"], [\"2\", \"0\", \"4\"]],
  [[\"1\", \"1\"], [\"1\", \"1\", \"5\"]],
  [[\"2\", \"1\"], [\"2\", \"1\", \"2\"]],
  [[\"1\", \"1\"], [\"1\", \"2\", \"3\"]]],
 \"_type\": {\"params\": \"Rat\", \"name\": \"Polynomial\"},
 \"_ns\": {\"Lean\": [\"https://github.com/leanprover/lean4\", \"4.33.1\"]}}"
S = ring f
assert Equation(numgens S, 3)
(x, y, z) = toSequence gens S
assert Equation(f, 2*x^2*z^4 + x*y*z^5 + 2*x^2*y*z^2 + x*y^2*z^3)
///

-----------------------
-- LSP-style framing --
-----------------------

TEST ///
debug Macaulean
withFile = (contents, f) -> (
    fn := temporaryFileName();
    fn << contents << close;
    file := openIn fn;
    first(f file, close file, removeFile fn))

withFile("Content-Length: 42\r\nContent-Type: application/json\r\n\r\nbody",
    file -> (
        h := readLSPHeaders file;
        assert Equation(h#"Content-Length", "42");
        assert Equation(h#"Content-Type", "application/json");
        assert Equation(read(file, 4), "body")))

-- whitespace around header values is stripped
withFile("Content-Length:   17  \r\n\r\n",
    file -> assert Equation((readLSPHeaders file)#"Content-Length", "17"))

-- only CRLF ends a header line; a lone CR is kept
withFile("Content-Length: 4\rextra\r\n\r\nbody",
    file -> (
        assert Equation(readLSPHeaderLine file, "Content-Length: 4\rextra");
        assert Equation(readLSPHeaderLine file, ""); -- end of the headers
        assert Equation(read(file, 4), "body")))
///

----------------------
-- JSON-RPC methods --
----------------------

TEST ///
-- ideal membership via the quotientRemainder method
needsPackage "JSON"
server = macauleanServer()
mrdi = f -> saveMRDI(new ConcretePoly from f, Namespace => "Lean",
    ToString => false)
qr = (f, I) -> (
    request := makeRequest("quotientRemainder",
        {mrdi f, apply(first entries gens I, mrdi)}, 1);
    result := (fromJSON handleRequest(server, request))#"result";
    -- polynomials come back in rings with (possibly) fewer variables
    R := ring f;
    toR := g -> (
        if instance(g, ZZ) then promote(g, R)
        else (map(R, ring g, (gens R)_{0..<numgens ring g})) g);
    (apply(result#"quotient", g -> toR loadMRDI toJSON g),
        toR loadMRDI toJSON result#"remainder"))

-- f is in the ideal, so r is 0 and q is a certificate of membership
R = QQ[x,y,z]
I = ideal(x*z, y)
f = x*z^2
(q, r) = qr(f, I)
assert zero r
assert Equation(#q, numgens I)
assert Equation(f, sum(#q, i -> q#i * I_i))

-- g is not in the ideal, so there's a nonzero remainder
S = QQ[x,y]
J = ideal(x^2)
g = x + y
(q, r) = qr(g, J)
assert not zero r
assert Equation(g, sum(#q, i -> q#i * J_i) + r)
///

TEST ///
-- the remaining methods
needsPackage "JSON"
server = macauleanServer()
call = (m, params) -> (
    (fromJSON handleRequest(server, makeRequest(m, params, 1)))#"result")

-- testMethod evaluates an M2 expression
assert Equation(call("testMethod", {"2 + 2"}), "4")

-- factorInt takes and returns plain JSON
assert Equation(call("factorInt", {12}), {{2, 2}, {3, 1}})

-- mrdiFactor takes MRDI and returns each factor as a string of MRDI
R = QQ[x,y]
f = x^2 - y^2
result = call("mrdiFactor",
    {saveMRDI(f, Namespace => "Lean", ToString => false)})
toR = g -> (map(R, ring g, (gens R)_{0..<numgens ring g})) g
L = apply(result, term -> (toR loadMRDI term#0, term#1))
assert Equation(f, product(L, term -> term#0^(term#1)))
///

TEST ///
-- a bad request shouldn't take down the server
needsPackage "JSON"
server = macauleanServer()
err = (m, params) -> (
    (fromJSON handleRequest(server, makeRequest(m, params, 1)))#"error"#"code")

assert Equation(err("nosuchmethod", {}), -32601)
assert Equation(err("quotientRemainder", {"not json", {}}), -32603)
assert Equation(err("mrdiEcho", {"not json"}), -32603)

-- and it's still usable afterwards
assert Equation(
    (fromJSON handleRequest(server, makeRequest("testMethod", {"1 + 1"}, 2)))#
    "result", "2")
///

----------------
-- end to end --
----------------

TEST ///
-- drive macauleanStart in a separate M2 process, just like the Lean side
needsPackage "JSON"

startfile = temporaryFileName() | ".m2"
startfile << "loadPackage(\"Macaulean\", FileName => \"" <<
    Macaulean#"source file" << "\", Reload => true)" << endl <<
    "macauleanStart()" << endl << close
server = openInOut("!" | commandLine#0 | " --script " | startfile)

send = request -> (
    server << "Content-Length: " << #request << "\r\n\r\n" << request << flush;)
readLine = () -> concatenate delete(null,
    while not atEndOfFile server list (
        c := getc server;
        if c == "\n" then break;
        if c != "\r" then c))
receive = () -> (
    n := null;
    while (line := readLine()) != "" do
        if match("^Content-Length:", line)
        then n = value replace(".*: *", "", line);
    if n === null then error "no Content-Length header in response";
    concatenate while n > 0 list (
        block := read(server, n);
        if #block == 0 then error "truncated response";
        n -= #block;
        block))
call = (m, params) -> (
    send makeRequest(m, params, 1);
    response := fromJSON receive();
    if response#?"error" then error response#"error"#"message";
    response#"result")

assert Equation(call("testMethod", {"2 + 2"}), "4")
assert Equation(call("factorInt", {12}), {{2, 2}, {3, 1}})

-- the child's UUID cache is empty, so this is a cross-session round trip
R = QQ[x,y,z]
I = ideal(x*z, y)
f = x*z^2
mrdi = g -> saveMRDI(new ConcretePoly from g, Namespace => "Lean",
    ToString => false)
result = call("quotientRemainder", {mrdi f, apply(first entries gens I, mrdi)})
toR = g -> (
    if instance(g, ZZ) then promote(g, R)
    else (map(R, ring g, (gens R)_{0..<numgens ring g})) g)
r = toR loadMRDI toJSON result#"remainder"
q = apply(result#"quotient", g -> toR loadMRDI toJSON g)
assert zero r
assert Equation(f, sum(#q, i -> q#i * I_i))

close server
removeFile startfile
///
