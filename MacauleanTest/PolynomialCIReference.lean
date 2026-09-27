import MacauleanTest.NativePolynomialOracle
import Macaulean.Interpreter.KernelPolynomial

open Macaulean.M2
#print axioms Macaulean.Polynomial.normalize
#print axioms Macaulean.Polynomial.sortTerms
#print axioms Macaulean.Polynomial.coalesceTerms
#print axioms Macaulean.Polynomial.add
#print axioms Macaulean.M2.KernelPolynomial.add
#print axioms Macaulean.M2.Polynomials.normalized

#eval do
  for src in [
    "R=QQ[x,y,z];ring x==R",
    "R=QQ[x,y,z];ring x===R",
    "R=QQ[x,y,z];coefficientRing R==QQ",
    "R=QQ[x,y,z];ring ideal(x,y)==R",
    "R=QQ[x];S=QQ[x];R==S",
    "R=QQ[x];S=R;R==S",
    "R=QQ[x];p=x;S=QQ[x];ring p==R",
    "x=91;R=QQ[x];exponents x",
    "x=3;R=QQ[x];numgens R",
    "local x;R=QQ[x];x",
    "local x;R=QQ[x];numgens R",
    "x:=13;R=QQ[x];x",
    "f=x->(R=QQ[x];numgens R);f 3",
    "calls=0;K=()->(calls=calls+1;QQ);R=(K())[x,y];calls",
    "R=QQ[x,y];listForm((promote(2,R))^(-2))",
    "QQ[x,x]",
    "R=QQ[x];(x^2)/x",
    "R=QQ[x];degree(0*x)",
    "R=QQ[x];leadMonomial(0*x)",
    "R=QQ[x];old=x;S=QQ[old];{numgens S,ring old===S,ring x===R}"
  ] do
    let result ← NativePolynomialOracle.raw s!"({src})" true
    IO.println s!"POLYNOMIAL_FRESH_REFERENCE {repr src}: {repr result}"
