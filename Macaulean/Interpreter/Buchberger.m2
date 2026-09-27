-- Buchberger over QQ with the fixed global grevlex order.
-- This file is the algorithm. The Lean backend supplies polynomial arithmetic,
-- leading terms, exact monomial operations, and checked result containers only.
-- A represented polynomial is {p, row}, with p = sum(row_i * input_i).

m2gbScaleRow = (c,row,i) ->
    if i == #row then {} else {c*(row#i)} | m2gbScaleRow(c,row,i+1);

m2gbSubtractRow = (row,c,other,i) ->
    if i == #row then {} else
    {row#i-c*(other#i)} | m2gbSubtractRow(row,c,other,i+1);

m2gbUnitRow = (R,n,j,i) ->
    if i == n then {} else
    {promote(if i == j then 1 else 0,R)} | m2gbUnitRow(R,n,j,i+1);

m2gbMonic = pair -> (
    p := pair#0;
    if p == 0 then pair else (
        c := 1/(leadCoefficient p);
        {c*p,m2gbScaleRow(c,pair#1,0)}));

m2gbInitial = (F,R,i) ->
    if i == #F then {} else
    if F#i == 0 then m2gbInitial(F,R,i+1) else
    {m2gbMonic {F#i,m2gbUnitRow(R,#F,i,0)}} | m2gbInitial(F,R,i+1);

-- Select the first divisor in the supplied order; zero generators are absent.
m2gbReducer = (h,G,j) ->
    if j == #G then -1 else
    if m2MonomialDivides(leadMonomial ((G#j)#0),leadMonomial h)
    then j else m2gbReducer(h,G,j+1);

-- row always represents h + remainder in the original input generators.
m2gbReduce = (h,row,G,remainder) ->
    if h == 0 then {remainder,row} else (
        j := m2gbReducer(h,G,0);
        if j < 0 then (
            t := leadTerm h;
            m2gbReduce(h-t,row,G,remainder+t))
        else (
            g := G#j;
            c := (leadCoefficient h)/(leadCoefficient (g#0)) *
                 m2MonomialQuotient(leadMonomial h,leadMonomial (g#0));
            m2gbReduce(h-c*(g#0),m2gbSubtractRow(row,c,g#1,0),G,remainder)));

m2gbSPair = (a,b) -> (
    f := a#0;
    g := b#0;
    L := m2MonomialLCM(leadMonomial f,leadMonomial g);
    u := m2MonomialQuotient(L,leadMonomial f)/(leadCoefficient f);
    v := m2MonomialQuotient(L,leadMonomial g)/(leadCoefficient g);
    {u*f-v*g,m2gbSubtractRow(m2gbScaleRow(u,a#1,0),v,b#1,0)});

m2gbNewPairs = (k,i) ->
    if i >= k then {} else {(i,k)} | m2gbNewPairs(k,i+1);

m2gbPairs = (n,k) ->
    if k >= n then {} else m2gbNewPairs(k,0) | m2gbPairs(n,k+1);

-- Append new pairs, but never forget pending old pairs. Each nonzero remainder
-- strictly enlarges the leading ideal in the mathematical algorithm.
m2gbLoop = (G,pairs,pos) ->
    if pos >= #pairs then G else (
        ij := pairs#pos;
        s := m2gbSPair(G#(ij#0),G#(ij#1));
        h := m2gbReduce(s#0,s#1,G,0*(s#0));
        if h#0 == 0 then m2gbLoop(G,pairs,pos+1) else (
            k := #G;
            m2gbLoop(G | {m2gbMonic h},pairs | m2gbNewPairs(k,0),pos+1)));

-- Equal leading monomials keep the earlier generator, so duplicates cannot
-- eliminate one another simultaneously.
m2gbRedundant = (G,i,j) ->
    if j == #G then false else
    if i == j then m2gbRedundant(G,i,j+1) else (
        a := leadMonomial ((G#i)#0);
        b := leadMonomial ((G#j)#0);
        if m2MonomialDivides(b,a) and (a != b or j < i)
        then true else m2gbRedundant(G,i,j+1));

m2gbMinimal = (G,i) ->
    if i == #G then {} else
    if m2gbRedundant(G,i,0) then m2gbMinimal(G,i+1) else
    {G#i} | m2gbMinimal(G,i+1);

m2gbWithout = (xs,k,i) ->
    if i == #xs then {} else
    if i == k then m2gbWithout(xs,k,i+1) else
    {xs#i} | m2gbWithout(xs,k,i+1);

m2gbInterreduce = (G,i) ->
    if i == #G then {} else (
        a := G#i;
        h := m2gbReduce(a#0,a#1,m2gbWithout(G,i,0),0*(a#0));
        {m2gbMonic h} | m2gbInterreduce(G,i+1));

m2gbTail = (xs,i) ->
    if i == #xs then {} else {xs#i} | m2gbTail(xs,i+1);

m2gbInsert = (a,xs,i) ->
    if i == #xs then {a} else
    if m2MonomialCompare(a#0,(xs#i)#0) <= 0 then {a} | m2gbTail(xs,i) else
    {xs#i} | m2gbInsert(a,xs,i+1);

m2gbSort = (xs,i) ->
    if i == #xs then {} else m2gbInsert(xs#i,m2gbSort(xs,i+1),0);

m2gbMain = input -> (
    I := m2AsIdeal input;
    F := m2GeneratorList I;
    initial := m2gbInitial(F,ring I,0);
    completed := m2gbLoop(initial,m2gbPairs(#initial,0),0);
    minimal := m2gbMinimal(completed,0);
    reduced := m2gbInterreduce(minimal,0);
    m2MakeBasis(I,m2gbSort(reduced,0)));

-- Normal form and S-polynomial exports use the same reduction code as gb.
m2gbBarePairs = (F,R,i) ->
    if i == #F then {} else (
        p := promote(F#i,R);
        if p == 0 then m2gbBarePairs(F,R,i+1) else
        {{p,{}}} | m2gbBarePairs(F,R,i+1));

m2gbNormalForm = (f,G) -> (
    leadCoefficient f;
    F := m2GeneratorList G;
    (m2gbReduce(f,{},m2gbBarePairs(F,ring f,0),0*f))#0);

m2gbSPolynomial = (f,g) -> (m2gbSPair({f,{}},{g,{}}))#0;
