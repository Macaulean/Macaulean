import MacauleanTest.NativePolynomialOracle
import Macaulean.Interpreter.KernelPolynomial

open Macaulean.M2

#eval do
  for src in [
    "x=3;R=QQ[x];{numgens R,gens R,x}",
    "x=0;R=QQ[x];{numgens R,gens R,x}",
    "x=-1;R=QQ[x];numgens R",
    "local x;R=QQ[x,y];{numgens R,gens R,x,y}",
    "f=x->(R=QQ[x];{numgens R,gens R,x});f 3",
    "x=2;R=QQ[x,y];{numgens R,gens R,x,y}",
    "x=2;y=2;R=QQ[x,y];{numgens R,gens R,x,y}",
    "R=QQ[x,y];old=x;S=QQ[old];{numgens S,gens S,ring old===R,ring x===S}",
    "R=QQ[x,y];old=x+y;S=QQ[old];{numgens S,gens S}",
    "local x;R=QQ[local x];{numgens R,gens R,ring x===R}",
    "{1===1/1,1=!=1/1,{1}==={1},(1,2)===(1,2)}",
    "R=QQ[x];{x===x+0,1===promote(1,R),promote(1,R)===promote(1,R)}",
    "R=QQ[x];{QQ===QQ,R===R,QQ===R,QQ=!=R}",
    "R=QQ[x];f=x->x;{f===f,(x->x)===(x->x)}",
    "R=QQ[x];{(gens ideal(x))===(gens ideal(x))}",
    "R=QQ[x];{ideal(x)===ideal(x),ideal(x)===ideal(2*x)}"
  ] do
    let result ← NativePolynomialOracle.raw s!"({src})" true
    IO.println s!"POLYNOMIAL_FRESH_REFERENCE {repr src}: {repr result}"
