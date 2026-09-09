newPackage(
    "Macaulean",
    Version => "0.1.0",
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
    HomePage => "https://github.com/Macaulean/Macaulean",
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
	    "coefficients" => apply(pairs coeffmap, (a, i) -> {i, a}),
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
		    (R_(varmap#var))^pow ?? coeffmap#var))))

------------------------------------------
-- MRDI serialization & deserialization --
------------------------------------------

addNamespace("Macaulean", "https://github.com/Macaulean/Macaulean",
    (options Macaulean).Version)

addSaveMethod(RingElement,
    f -> leanRings#(coefficientRing ring f),
    f -> apply(listForm f, (m, c) -> {toLean c, m}),
    Name => "Polynomial",
    Namespace => "Macaulean")

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
    Namespace => "Macaulean")

addSaveMethod(LeanGrindCommRingPoly,
    toList,
    Name => "Lean.Grind.CommRing.Poly",
    Namespace => "Macaulean",
    UseID => true)

addSaveMethod(ConcretePoly,
    f -> f#"params",
    f -> hashTable {
	"poly" => f#"poly",
	"coefficients" => f#"coefficients"},
    Namespace => "Macaulean")

addLoadMethod("Lean.Grind.CommRing.Poly",
    (params, data) -> LeanGrindCommRingPoly apply(data, term -> {
	    value term#0,
	    apply(term#1, varpow -> value \ varpow)}),
    Namespace => "Macaulean")

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
    Namespace => "Macaulean")


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
			Namespace => "Macaulean",
			ToString => false)),
		"remainder" => saveMRDI(r_(0,0),
		    Namespace => "Macaulean",
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
	    saveMRDI(f, Namespace => "Macaulean")));

    registerMethod(server, "mrdiFactor", (mrdi) -> (
	    f := loadMRDI mrdi;
	    stderr << f << endl;
	    apply(toList \ toList factor f, term -> (
		    saveMRDI(term#0, Namespace => "Macaulean"), term#1))));

    server)

macauleanStart = () -> macauleanMainLoop(macauleanServer(), stdio);

beginDocumentation()

doc ///
  Key
    Macaulean
  Headline
    Macaulay2 <-> Lean interface
  Description
    Text
      This package is the Macaulay2 half of
      @HREF("https://github.com/Macaulean/Macaulean", "Macaulean")@, an
      interface between Macaulay2 and the
      @HREF("https://lean-lang.org/", "Lean")@ theorem prover.  The Lean half
      provides tactics which, on appropriate goals, ask Macaulay2 to perform a
      computation and then use the result of that computation to produce a
      proof of the goal.  Ideal membership and factorization are the first
      targets.
    Text
      Macaulay2 acts as an oracle.  Lean starts it as a subprocess along the
      lines of
    Pre
      M2 --stop --no-debug --silent -q \
         -e 'needsPackage "Macaulean"' \
         -e 'macauleanStart()' \
         -e 'exit 0'
    Text
      and then talks to it over its standard input and output.  The
      conversation is a @TO2("JSONRPC::JSONRPC", "JSON-RPC 2.0")@ exchange in
      which each message is preceded by a @SAMP "Content-Length"@ header,
      exactly as in the base protocol of the
      @HREF("https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#baseProtocol",
	  "Language Server Protocol")@.  See @TO macauleanStart@ for the loop
      that reads these messages and @TO macauleanServer@ for the methods that
      may be called.
    Text
      Mathematical objects travel across the wire in the
      @TO2("MRDI::MRDI", "mrdi file format")@, using types registered in a
      Macaulean namespace so that both systems agree on their meaning.  See
      @TO "the Macaulean MRDI namespace"@.
    Example
      server = macauleanServer()
      handleRequest(server, makeRequest("factorInt", {12}, 1))
  Acknowledgement
    This work is supported by the
    @HREF("https://www.renaissancephilanthropy.org/ai-for-math-fund/",
	"AI for Math Fund")@ as part of the project
    @HREF("https://www.renaissancephilanthropy.org/bridging-proof-and-computation-a-verified-leanmacaulay2-interface",
	"Bridging proof and computation: a verified Lean/Macaulay2 interface")@.
  Citation
    @unpublished{Ballard2026Macaulay2Lean,
      author = {Matthew Ballard and
                Anton Leykin and
                Michael E. Stillman and
                Damiano Testa and
                Douglas A. Torrance and
                Jay Yang},
      title  = {A Macaulay2-Lean Interface for Proofs in Lean},
      note   = {Accepted for publication in Lecture Notes in Computer Science (ICMS 2026)},
      year   = {2026},
      url    = {https://icms-conference.org/2026/papers/paper13/main.pdf}
    }
  Subnodes
    "the Macaulean MRDI namespace"
    ConcretePoly
    LeanGrindCommRingPoly
    macauleanServer
    macauleanStart
///

doc ///
  Key
    "the Macaulean MRDI namespace"
  Headline
    types used to exchange polynomials with Lean
  Description
    Text
      Objects sent between Macaulay2 and Lean are serialized using the
      @TO2("MRDI::MRDI", "mrdi file format")@.  This package registers the
      namespace @SAMP "Macaulean"@ together with the three types below;
      passing @CODE "Namespace => \"Macaulean\""@ to
      @TO "MRDI::saveMRDI"@ selects them.  Since each type is also implemented
      on the Lean side, the two systems can agree on what they are looking at.
    Text
      Two of them, @SAMP "Polynomial"@ and @SAMP "ConcretePoly"@, take a
      parameter naming the coefficient ring, using Lean's name for it:
      @SAMP "Int"@ for @TO ZZ@ and @SAMP "Rat"@ for @TO QQ@.
      As the mrdi format requires, integers are serialized as strings, and a
      rational number is serialized as a pair of strings giving its numerator
      and denominator.  Variables are referred to by their index rather than
      by name.
    Text
      @HEADER3 "Polynomial"@
    Text
      A @TO RingElement@ is serialized as a @SAMP "Polynomial"@, a list of
      @CODE "{coefficient, exponents}"@ pairs, one for each term, where
      @VAR "exponents"@ is the term's exponent vector, as in @TO listForm@ but
      with the coefficient first.  This is the type in which the server
      returns its answers.
    Example
      R = QQ[x,y,z]
      f = x*z^2 - 3/2*y
      saveMRDI(f, Namespace => "Macaulean")
    Text
      Nothing in this format records the number of variables of the ring, so
      trailing variables which do not appear in any term are lost; the ring
      reconstructed by @TO "MRDI::loadMRDI"@ has only as many variables as the
      exponent vectors do.  In particular, the zero polynomial has no terms at
      all, and so comes back as the integer zero.
    Example
      loadMRDI saveMRDI(f, Namespace => "Macaulean")
      loadMRDI saveMRDI(0_R, Namespace => "Macaulean")
    Text
      @HEADER3 "Lean.Grind.CommRing.Poly"@
    Text
      A @TO LeanGrindCommRingPoly@ is serialized as a
      @SAMP "Lean.Grind.CommRing.Poly"@, mirroring the type of the same name
      used by Lean's @CODE "grind"@ tactic.  It is a list of
      @CODE "{coefficient, monomial}"@ pairs, where a @VAR "monomial"@ is a
      list of @CODE "{variable, exponent}"@ pairs; only the variables actually
      occurring in the monomial are listed.  It is saved with
      @CODE "UseID => true"@, so it appears among the @SAMP "_refs"@ of
      whatever object contains it rather than inline.
    Text
      @HEADER3 "ConcretePoly"@
    Text
      A @TO ConcretePoly@ is serialized as a @SAMP "ConcretePoly"@, a hash
      table with two keys: @SAMP "poly"@, a reference to a
      @SAMP "Lean.Grind.CommRing.Poly"@, and @SAMP "coefficients"@, a list of
      @CODE "{variable, value}"@ pairs.  A @SAMP "Lean.Grind.CommRing.Poly"@
      has integer coefficients, so a coefficient which is not an integer is
      recorded here as an extra variable instead; see @TO ConcretePoly@.
    Example
      cp = new ConcretePoly from f
      saveMRDI(cp, Namespace => "Macaulean")
  SeeAlso
    "MRDI::addNamespace"
    "MRDI::validateMRDI"
    "MRDI::Namespace"
///

doc ///
  Key
    ConcretePoly
  Headline
    the class of all Lean concrete polynomials
  Description
    Text
      A @TO ConcretePoly@ is a @TO LeanGrindCommRingPoly@ together with an
      interpretation of some of its variables as coefficients.  Lean's
      @SAMP "Lean.Grind.CommRing.Poly"@ has integer coefficients only, so a
      polynomial over a larger ring is represented by moving each offending
      coefficient into a new variable and remembering its value on the side.
    Text
      It is a @TO SelfInitializingType@ of @TO HashTable@ with three keys.
    Text
      @UL {
	  LI {CODE "\"poly\"", ", a ", TO LeanGrindCommRingPoly},
	  LI {CODE "\"coefficients\"", ", a list of ",
	      CODE "{variable, value}", " pairs giving the values of those
	      variables which are really coefficients"},
	  LI {CODE "\"params\"", ", the name Lean uses for the coefficient
	      ring, either ", SAMP "Int", " or ", SAMP "Rat"}}@
    Example
      R = QQ[x,y,z]
      peek new ConcretePoly from x*z^2 - 3/2*y
    Text
      Here @CODE "x*z^2"@ has integer coefficient 1 and is stored as it
      stands, but @CODE "-3/2"@ cannot be, so it becomes the variable with
      index 3, one past the variables of @VAR "R"@, whose value
      @CODE "{-3, 2}"@ is recorded under @CODE "\"coefficients\""@.
    Text
      Objects of this class may be serialized and deserialized in the
      @TO "the Macaulean MRDI namespace"@.
  SeeAlso
    LeanGrindCommRingPoly
  Subnodes
    (NewFromMethod, ConcretePoly, RingElement)
    (value, ConcretePoly)
///

doc ///
  Key
    (NewFromMethod, ConcretePoly, RingElement)
  Headline
    convert a ring element to a Lean concrete polynomial
  Usage
    new ConcretePoly from f
  Inputs
    f:RingElement -- in a polynomial ring over @TO ZZ@ or @TO QQ@
  Outputs
    :ConcretePoly
  Description
    Text
      The terms of @VAR "f"@ become the terms of the underlying
      @TO LeanGrindCommRingPoly@.  Coefficients which lift to @TO ZZ@ are used
      as they are.  Each of the others is assigned a variable, numbered
      consecutively starting from @TO numgens@ of the ring of @VAR "f"@, and
      the term is rewritten as that variable times the remaining monomial.
    Example
      R = ZZ[x,y]
      peek new ConcretePoly from x^2 + 3*y - 1
    Text
      Over @TO QQ@ every coefficient which is not an integer needs a variable
      of its own, but equal coefficients share one.
    Example
      S = QQ[x,y]
      peek new ConcretePoly from 1/2*x^2 + 1/2*y
  SeeAlso
    (value, ConcretePoly)
    listForm
///

doc ///
  Key
    (value, ConcretePoly)
  Headline
    convert a Lean concrete polynomial to a ring element
  Usage
    value f
  Inputs
    f:ConcretePoly
  Outputs
    :RingElement
  Description
    Text
      Each variable of @VAR "f"@ which is listed under
      @CODE "\"coefficients\""@ is replaced by its value, and the rest become
      the variables of a new polynomial ring over @TO ZZ@ or @TO QQ@,
      according to @CODE "f#\"params\""@.
    Example
      R = QQ[x,y,z]
      f = x*z^2 - 3/2*y
      value new ConcretePoly from f
    Text
      Note that the ring returned is not the ring of the polynomial we started
      with.  Only those variables which occur in some term of @VAR "f"@ appear
      in it, and they are renamed accordingly, so a map is needed to compare
      the two.
    Example
      g = value new ConcretePoly from f
      describe ring g
      (map(R, ring g, {x, y, z})) g == f
  SeeAlso
    (NewFromMethod, ConcretePoly, RingElement)
///

doc ///
  Key
    LeanGrindCommRingPoly
  Headline
    the class of all Lean grind commutative ring polynomials
  Description
    Text
      This class represents Lean's @SAMP "Lean.Grind.CommRing.Poly"@, the
      normal form for polynomials with integer coefficients used by Lean's
      @CODE "grind"@ tactic.  It is a @TO SelfInitializingType@ of @TO List@,
      each element of which is a pair @CODE "{coefficient, monomial}"@ where
      the monomial is itself a list of pairs @CODE "{variable, exponent}"@,
      listing only those variables which actually occur.
    Example
      p = LeanGrindCommRingPoly {{3, {}}, {5, {{2, 3}}}}
    Text
      So @VAR "p"@ is @CODE "3 + 5*x_2^3"@.  Such an object is usually met as
      the @CODE "\"poly\""@ key of a @TO ConcretePoly@, which is how
      coefficients outside of @TO ZZ@ are accommodated.
    Example
      R = QQ[x,y,z]
      (new ConcretePoly from x*z^2 - 3/2*y)#"poly"
    Text
      Objects of this class may be serialized and deserialized in the
      @TO "the Macaulean MRDI namespace"@.
  SeeAlso
    ConcretePoly
///

doc ///
  Key
    macauleanServer
  Headline
    create a JSON-RPC server for Lean
  Usage
    macauleanServer()
  Outputs
    :JSONRPCServer
  Description
    Text
      This function returns a new @TO "JSONRPC::JSONRPCServer"@ with the
      methods that Macaulean's Lean tactics call.  It is a function rather
      than a global variable so that each caller gets a server of its own.
    Example
      server = macauleanServer()
      methods server
    Text
      Requests may be handed to it directly using
      @TO "JSONRPC::handleRequest"@, which is convenient for testing;
      @TO macauleanStart@ does so in a loop, reading the requests from
      standard input.
    Text
      @HEADER3 "quotientRemainder"@
    Text
      Given a polynomial and a list of polynomials generating an ideal, all
      serialized in @TO "the Macaulean MRDI namespace"@, this method returns a
      hash table with keys @SAMP "quotient"@ and @SAMP "remainder"@, the
      result of dividing the polynomial by the generators.  If the remainder
      is zero, then the quotient is a certificate that the polynomial belongs
      to the ideal, and it is this certificate which the Lean side turns into
      a proof.
    Example
      R = QQ[x,y,z]
      lean = f -> saveMRDI(f, Namespace => "Macaulean", ToString => false)
      handleRequest(server, makeRequest("quotientRemainder",
	      {lean(x*z^2), {lean(x*z), lean y}}, 1))
    Text
      @HEADER3 "factorInt"@
    Text
      Given an integer, this method returns its factorization as a list of
      @CODE "{prime, exponent}"@ pairs.  No mrdi is involved; the integers are
      sent as plain JSON.
    Example
      handleRequest(server, makeRequest("factorInt", {12}, 2))
    Text
      @HEADER3 "mrdiFactor"@
    Text
      Given a polynomial serialized in
      @TO "the Macaulean MRDI namespace"@, this method returns its
      factorization as a list of @CODE "{factor, exponent}"@ pairs, where each
      factor is again serialized.
    Example
      handleRequest(server, makeRequest("mrdiFactor", {lean(x^2 - y^2)}, 3))
    Text
      @HEADER3 "mrdiEcho"@
    Text
      Given an object serialized in @TO "the Macaulean MRDI namespace"@, this
      method prints it to standard error and hands it back, serialized again.
      It is useful for checking that the two systems read each other's mrdi
      the way they are meant to.
    Text
      @HEADER3 "testMethod"@
    Text
      Given a string, this method evaluates it as a Macaulay2 expression and
      returns @TO toExternalString@ of the result.
    Example
      handleRequest(server, makeRequest("testMethod", {"2 + 2"}, 4))
  Caveat
    The @SAMP "quotientRemainder"@ method returns its polynomials as JSON
    objects, but @SAMP "mrdiFactor"@ and @SAMP "mrdiEcho"@ return theirs as
    strings containing JSON, which must be parsed a second time.

    A @SAMP "factor"@ method is registered as well, but it is not yet working:
    it tries to serialize a list, for which no save method exists.
  SeeAlso
    macauleanStart
    "JSONRPC::registerMethod"
///

doc ///
  Key
    macauleanStart
  Headline
    run a JSON-RPC server for Lean on standard input and output
  Usage
    macauleanStart()
  Description
    Text
      This function creates a @TO macauleanServer@ and then serves requests
      read from @TO stdio@ until end of file, writing each response back to
      it.  It is what Lean asks Macaulay2 to do when it starts it as a
      subprocess.
    Pre
      M2 --stop --no-debug --silent -q \
         -e 'needsPackage "Macaulean"' \
         -e 'macauleanStart()' \
         -e 'exit 0'
    Text
      Requests and responses are framed as in the base protocol of the
      @HREF("https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#baseProtocol",
	  "Language Server Protocol")@: a @SAMP "Content-Length"@ header giving
      the number of bytes in the message, any number of further headers, a
      blank line, and then the message itself, with every line ending in
      @SAMP "\\r\\n"@.  Only @SAMP "Content-Length"@ is looked at; the other
      headers are read and ignored.
    Text
      So a session on the terminal, were one to hold it by hand, would begin
    Pre
      Content-Length: 66

      {"jsonrpc": "2.0", "id": 1, "method": "factorInt", "params": [12]}
  SeeAlso
    macauleanServer
    "JSONRPC::handleRequest"
///
----------------------------------
-- ConcretePoly <-> RingElement --
----------------------------------

TEST ///
-- ConcretePoly round trips
-- MRDI would hand back the object we just saved, so make it forget the UUID's
debug MRDI
roundTrip = f -> (
    mrdi := saveMRDI(new ConcretePoly from f, Namespace => "Macaulean");
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
g = loadMRDI saveMRDI(f, Namespace => "Macaulean")
assert Equation(f, (map(R, ring g, vars R)) g)

S = ZZ[x,y,z]
h = x*z^2 - 3*y
k = loadMRDI saveMRDI(h, Namespace => "Macaulean")
assert Equation(h, (map(S, ring k, vars S)) k)

-- the zero polynomial carries no ring information
z0 = loadMRDI saveMRDI(0_R, Namespace => "Macaulean")
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
mrdi = fromJSON saveMRDI(new ConcretePoly from x + 1/2*y, Namespace => "Macaulean")
assert Equation(mrdi#"_type"#"name", "ConcretePoly")
assert Equation(mrdi#"_type"#"params", "Rat")
assert Equation(first keys mrdi#"_ns", "Macaulean")
-- the underlying Lean.Grind.CommRing.Poly is stored as a reference
assert Equation(#mrdi#"_refs", 1)
assert Equation((first values mrdi#"_refs")#"_type", "Lean.Grind.CommRing.Poly")

mrdi = fromJSON saveMRDI(x + 1/2*y, Namespace => "Macaulean")
assert Equation(mrdi#"_type"#"name", "Polynomial")
assert Equation(mrdi#"_type"#"params", "Rat")
///

TEST ///
-- everything we serialize must be valid MRDI
needsPackage "JSON"
lean = x -> saveMRDI(x, Namespace => "Macaulean", ToString => false)

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
 \"_ns\": {\"Macaulean\": [\"https://github.com/Macaulean/Macaulean\", \"0.1.0\"]}}"
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
 \"_ns\": {\"Macaulean\": [\"https://github.com/Macaulean/Macaulean\", \"0.1.0\"]}}"
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
 \"_ns\": {\"Macaulean\": [\"https://github.com/Macaulean/Macaulean\", \"0.1.0\"]}}"
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
mrdi = f -> saveMRDI(new ConcretePoly from f, Namespace => "Macaulean",
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
    {saveMRDI(f, Namespace => "Macaulean", ToString => false)})
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
mrdi = g -> saveMRDI(new ConcretePoly from g, Namespace => "Macaulean",
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
