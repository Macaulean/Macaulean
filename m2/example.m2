-- JSON-RPC + MRDI examples

needsPackage "JSONRPC"
needsPackage "MRDI"
needsPackage "JSON"

----------------------
-- ideal membership --
----------------------

-- set up the server
server = new JSONRPCServer

registerMethod(server, "quotientRemainder", (polymrdi, idealmrdi) -> (
	f := loadMRDI polymrdi;
	I := loadMRDI idealmrdi;
	(q, r) := quotientRemainder(matrix f, gens I);
	(saveMRDI(q, ToString => false), saveMRDI(r, ToString => false))))
-- client constructs an ideal and a polynomial
R = QQ[x,y,z,w]
I = monomialCurveIdeal(R, {1,2,3})
f = random(2, I)
-- construct the JSON-RPC request
request = makeRequest("quotientRemainder",
    {saveMRDI(f, ToString => false), saveMRDI(I, ToString => false)}, 1)

-- server handles the computation
response = handleRequest(server, request)

-- client reads the result
result = (fromJSON response)#"result"
(q, r) = (loadMRDI result#0, loadMRDI result#1)
assert zero r -- ideal membership!
assert zero(gens I * q - matrix f) -- use q as our certificate

---------------------------
-- integer factorization --
---------------------------

registerMethod(server, "factor", (nmrdi) -> (
	n := loadMRDI nmrdi;
	saveMRDI(toList \ toList factor n, ToString => false)))

n = 2^(2^7) + 1 -- integer to factor

request = makeRequest("factor", {saveMRDI(n, ToString => false)}, 2)
response = handleRequest(server, request)

L = loadMRDI (fromJSON response)#"result"
assert(product(L, M -> M#0^(M#1)) == n)
