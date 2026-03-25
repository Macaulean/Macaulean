stderr << version << endl
stderr << "Macaulean M2 Startup" << endl

needsPackage "JSONRPC"
needsPackage "MRDI"
needsPackage "JSON"
needsPackage "Parsing"
needsPackage "SumsOfSquares"
--get the actual parser from the JSON package so we can run it character by character
importFrom_JSON {"jsonTextP"}
--get the helper function from JSONRPC that can take already parsed JSON objects
importFrom_JSONRPC {"handleRequestHelper"}

stderr << "Packages Loaded" << endl

mkZZRing = numVars -> ZZ[apply(numVars, i -> "x" | toString i)]
mkQQRing = numVars -> QQ[apply(numVars, i -> "x" | toString i)]

polyDataToRing = (R, data) -> (
    sum(apply(data, term -> (
        coeff := term#0;
        mon := term#1;
        coeff * product(mon, vp -> R_(vp#0)^(vp#1))
    )))
    )

polyToLeanData = f -> (
    monsAndCoeffs := coefficients f;
    mons := flatten entries first monsAndCoeffs;
    coeffs := flatten entries last monsAndCoeffs;
    apply(#mons, i -> (
        expVec := flatten exponents mons#i;
        {lift(coeffs#i, ZZ), apply(select(#expVec, j -> expVec#j != 0), j -> {j, expVec#j})}
    ))
    )

coeffDen = c -> denominator lift(c, QQ)

polyDenAndInt = f -> (
    coeffs := flatten entries last coefficients f;
    d := fold(apply(coeffs, coeffDen), 1, lcm);
    (d, d * f)
    )

sosCertificate = (numVars, polyData) -> (
    R := mkQQRing numVars;
    f := polyDataToRing(R, polyData);
    sol := solveSOS f;
    S := sosPoly sol;
    if S === null then return hashTable {
        "ok" => false,
        "status" => status sol,
        "scale" => 0,
        "summands" => {}
        };
    gensList := gens S;
    coeffList := coefficients S;
    factors := apply(#gensList, i -> (
        wi := coeffList#i;
        qi := gensList#i;
        (di, qiInt) := polyDenAndInt qi;
        denomFactor := denominator lift(wi, QQ) * di^2;
        hashTable {
            "weight" => numerator lift((denominator lift(wi, QQ) * wi), QQ),
            "denomFactor" => denomFactor,
            "poly" => polyToLeanData qiInt
            }
        ));
    scale := fold(apply(factors, t -> t#"denomFactor"), 1, lcm);
    summands := apply(factors, t -> hashTable {
        "weight" => scale // t#"denomFactor" * t#"weight",
        "poly" => t#"poly"
        });
    lhs := scale * f;
    rhs := sum(apply(summands, t -> (
        w := t#"weight";
        q := polyDataToRing(R, t#"poly");
        w * q^2
        )));
    if lhs =!= rhs then error "internal SOS certificate mismatch";
    hashTable {
        "ok" => true,
        "status" => status sol,
        "scale" => scale,
        "summands" => summands
        }
    )

quotientRemainderPolyData = (numVars, polyData, idealData) -> (
    R := mkZZRing numVars;
    f := polyDataToRing(R, polyData);
    gensList := apply(idealData, g -> polyDataToRing(R, g));
    I := ideal gensList;
    (q, r) := quotientRemainder(matrix{{f}}, gens I);
    quotients := flatten entries q;
    remainderEntries := flatten entries r;
    hashTable {
        "ok" => true,
        "status" => "ok",
        "quotients" => apply(quotients, polyToLeanData),
        "remainder" => if #remainderEntries == 0 then {{0, {}}} else polyToLeanData first remainderEntries
        }
    )



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
            requestBody := read(file,requestLength);
            response := handleRequest_server requestBody;
            file << "Content-Length: " << length response << "\r\n";
            file << "\r\n";
            file << response;
            )
        )
    )

--setup the server, copied from example.m2
server = new JSONRPCServer
server#"logger" = (str) -> (stderr << str << endl)
registerMethod(server, "quotientRemainder", (polymrdi, idealmrdi) -> (
	f := loadMRDI polymrdi;
	I := loadMRDI idealmrdi;
	(q, r) := quotientRemainder(matrix f, gens I);
	(saveMRDI q, saveMRDI r)))

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

registerMethod(server, "quotientRemainderPolyData", {"numVars", "polyData", "idealData"},
    (numVars, polyData, idealData) -> (
        quotientRemainderPolyData(numVars, polyData, idealData)
    )
)

registerMethod(server, "sosCertificate", {"numVars", "polyData"},
    (numVars, polyData) -> (
        sosCertificate(numVars, polyData)
    )
)

macauleanMainLoop(server, stdio);
-- inputJSON = fromJSONStream stdio;
-- stdio << toExternalString sum inputJSON << endl;

stderr << "Macaulay2 Finished" << endl
