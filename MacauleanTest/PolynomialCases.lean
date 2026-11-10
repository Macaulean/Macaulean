import Macaulean.Interpreter.Run

/-! Explicit expected data, independent of the polynomial implementation under test. -/
namespace Macaulean.M2.PolynomialCases

def listFormValue (ts : List (Rat × List Nat)) : Value :=
  .list (ts.map fun (c,ns) => .sequence [.list (ns.map fun n => .zz (Int.ofNat n)), .qq c])
def expsValue (ns : List (List Nat)) : Value :=
  .list (ns.map fun xs => .list (xs.map fun n => .zz (Int.ofNat n)))
def inXYZ (src : String) : String := "R=QQ[x,y,z];" ++ src

def arithmetic : List (String × Value) := [
  ("listForm(x+y)", listFormValue [(1,[1,0,0]),(1,[0,1,0])]),
  ("listForm((x+y)^2)", listFormValue [(1,[2,0,0]),(2,[1,1,0]),(1,[0,2,0])]),
  ("listForm((x-y)*(x+y))", listFormValue [(1,[2,0,0]),(-1,[0,2,0])]),
  ("listForm(x-x)", listFormValue []),
  ("listForm(0*x)", listFormValue []),
  ("listForm(x^0)", listFormValue [(1,[0,0,0])]),
  ("listForm(x+1/2)", listFormValue [(1,[1,0,0]),(mkRat 1 2,[0,0,0])]),
  ("listForm(1/2+x)", listFormValue [(1,[1,0,0]),(mkRat 1 2,[0,0,0])]),
  ("listForm(x/2+x/3)", listFormValue [(mkRat 5 6,[1,0,0])]),
  ("listForm(x/(1/2))", listFormValue [(2,[1,0,0])]),
  ("listForm((1/2)*x)", listFormValue [(mkRat 1 2,[1,0,0])]),
  ("listForm(2-x)", listFormValue [(-1,[1,0,0]),(2,[0,0,0])]),
  ("listForm(-(x-y))", listFormValue [(-1,[1,0,0]),(1,[0,1,0])]),
  ("listForm(+(x-y))", listFormValue [(1,[1,0,0]),(-1,[0,1,0])]),
  ("listForm((x+y+z)^2)", listFormValue [(1,[2,0,0]),(2,[1,1,0]),(1,[0,2,0]),(2,[1,0,1]),(2,[0,1,1]),(1,[0,0,2])]),
  ("exponents(x^2+y^2+x*z+y*z+z^2+x*y)", expsValue [[2,0,0],[1,1,0],[0,2,0],[1,0,1],[0,1,1],[0,0,2]]),
  ("(x+y)*z==x*z+y*z", .bool true),
  ("(x+y)^2==x^2+2*x*y+y^2", .bool true),
  ("x-x==0", .bool true),
  ("0==x-x", .bool true),
  ("promote(1,R)==1/1", .bool true),
  ("x!=y", .bool true),
  ("{x,1+x}=={x,1/1+x}", .bool true),
  ("listForm((promote(2,R))^(-2))", listFormValue [(mkRat 1 4,[0,0,0])]),
  ("listForm((x-x)^0)", listFormValue [(1,[0,0,0])]),
  ("listForm((promote(-2/3,R))^(-3))", listFormValue [(mkRat (-27) 8,[0,0,0])]),
  -- Native zero-polynomial powers are not the scalar division-by-zero cases.
  ("listForm((x-x)^(-1))", listFormValue []),
  ("listForm((x-x)^(-2))", listFormValue []),
  ("listForm((promote(0,R))^(-3))", listFormValue []),
  ("ring ((x-x)^(-1)) === R", .bool true),
  ("listForm((x^2+y)//x)", listFormValue [(1,[1,0,0])]),
  ("listForm((x^2+y)%x)", listFormValue [(1,[0,1,0])]),
  ("listForm((2*x^2+3*x*y+z)//(2*x))", listFormValue [(1,[1,0,0]),(mkRat 3 2,[0,1,0])]),
  ("listForm((2*x^2+3*x*y+z)%(2*x))", listFormValue [(1,[0,0,1])]),
  ("listForm((x+y)//2)", listFormValue [(mkRat 1 2,[1,0,0]),(mkRat 1 2,[0,1,0])]),
  ("listForm((x+y)%2)", listFormValue []),
  ("listForm((x-x)//x)", listFormValue [])
]

def interface : List (String × Value) := [
  ("numgens R", .zz 3),
  ("#gens R", .zz 3),
  ("ring x === R", .bool true),
  ("coefficientRing R === QQ", .bool true),
  ("listForm((gens R)#1)", listFormValue [(1,[0,1,0])]),
  ("leadCoefficient(3*x^2-y)", .qq 3),
  ("listForm(leadMonomial(3*x^2-y))", listFormValue [(1,[2,0,0])]),
  ("listForm(leadTerm(3*x^2-y))", listFormValue [(3,[2,0,0])]),
  ("leadCoefficient(x-x)", .qq 0),
  ("listForm(leadTerm(x-x))", listFormValue []),
  ("exponents(x-x)", .list []),
  ("terms(x-x)", .list []),
  ("size(x+x+y)", .zz 2),
  ("#terms(x^2+y+1)", .zz 3),
  ("listForm((terms(x^2+y+1))#1)", listFormValue [(1,[0,1,0])]),
  ("coefficient(x,x+y)", .qq 1),
  ("coefficient(x^2,3*x^2+x)", .qq 3),
  ("coefficient(x^2,x+y)", .qq 0),
  ("coefficient(promote(1,R),x+2/3)", .qq (mkRat 2 3)),
  ("numgens ideal(x,x,y)", .zz 3),
  ("numgens ideal(0*x,0*x)", .zz 2),
  ("numgens ideal{x,y}", .zz 2),
  ("ring ideal(x,y)===R", .bool true),
  ("#entries gens ideal(x,y)", .zz 1),
  ("#((entries gens ideal(x,y))#0)", .zz 2),
  ("listForm(((entries gens ideal(x^2-y,x*y-1))#0)#1)", listFormValue [(1,[1,1,0]),(-1,[0,0,0])]),
  ("numgens ideal gens ideal(x,y)", .zz 2),
  ("numgens ideal(x,2)", .zz 2),
  ("listForm(promote(0,R))", listFormValue []),
  ("lc=leadCoefficient;lc(5*x-y)", .qq 5),
  ("inspect=leadCoefficient@@leadTerm;inspect(7*x-y)", .qq 7),
  ("invoke=(f,p)->f p;invoke(exponents,x^2+y)", expsValue [[2,0,0],[0,1,0]]),
  ("p=x;old=p;p=p+y;old==x", .bool true)
]

def successes : List (String × Value) :=
  ((arithmetic ++ interface).map fun (s,v) => (inXYZ s,v)) ++ [
    ("R=QQ[];numgens R", .zz 0),
    ("R=QQ[];listForm(promote(3/2,R))", listFormValue [(mkRat 3 2,[])]),
    ("K=QQ;R=K[a,b];exponents(a+b)", expsValue [[1,0],[0,1]]),
    ("x=3;R=QQ[x];numgens R", .zz 3),
    ("local x;R=QQ[x];x", .null),
    ("x:=13;R=QQ[x];x", .zz 13),
    ("f=x->(R=QQ[x];x);f 3", .zz 3),
    ("calls=0;K=()->(calls=calls+1;QQ);R=(K())[x,y];calls", .zz 1),
    ("R=QQ[x];p=x;S=QQ[x];R === S", .bool false),
    ("R=QQ[x];S=R;R === S", .bool true),
    ("R=QQ[x];p=x;S=QQ[x];ring p === R", .bool true),
    ("R=QQ[x];p=x;S=QQ[x];ring p === S", .bool false),
    ("local x;R=QQ[x];numgens R", .zz 0),
    ("local x;R=QQ[x,y];numgens R", .zz 1),
    ("x=0;R=QQ[x];numgens R", .zz 0),
    ("x=-1;R=QQ[x];numgens R", .zz 0),
    ("f=x->(R=QQ[x];numgens R);f 3", .zz 3),
    ("x=3;R=QQ[x];x", .zz 3),
    ("x=3;R=QQ[x];exponents((gens R)#1)", expsValue [[0,1,0]]),
    ("R=QQ[x,y];old=x;S=QQ[old];ring old===R and ring x===S", .bool true),
    ("R=QQ[x];f=x->x;{f===f,(x->x)===(x->x)}", .list [.bool true,.bool false]),
    ("{1===1/1,1=!=1/1,{1}==={1},(1,2)===(1,2)}", .list [.bool false,.bool true,.bool true,.bool true]),
    ("R=QQ[x];{x===x+0,1===promote(1,R),QQ===QQ,R===R,QQ===R}", .list [.bool true,.bool false,.bool true,.bool true,.bool false]),
    ("R=QQ[x];{ideal(x)===ideal(x),ideal(x)===ideal(2*x)}", .list [.bool true,.bool false])
  ]

/-- Explicitly named helper APIs, not asserted to be native-library overloads. -/
def helpers : List (String × Value) :=
  List.map (fun (s,v) => (inXYZ s,v)) [
    ("m2MonomialDivides(x,x^2*y)", .bool true),
    ("m2MonomialDivides(x^2,x*y)", .bool false),
    ("m2MonomialDivides(2*x,3*x*y)", .bool true),
    ("listForm(m2MonomialQuotient(3*x^2*y,2*x))", listFormValue [(mkRat 3 2,[1,1,0])]),
    ("listForm(m2MonomialLCM(2*x^2,3*x*y))", listFormValue [(1,[2,1,0])]),
    ("m2MonomialCompare(x,y)", .zz 1),
    ("m2MonomialCompare(y,x)", .zz (-1)),
    ("m2MonomialCompare(2*x,3*x)", .zz 0),
    ("m2MonomialCompare(y^2,x*z)", .zz 1),
    ("listForm(m2Monomial(R,{2,0,3}))", listFormValue [(1,[2,0,3])]),
    ("listForm(m2Monomial(R,{0,0,0}))", listFormValue [(1,[0,0,0])])
  ]

def errors : List (String × Error) := [
  (inXYZ "x/0", .divByZero),
  (inXYZ "x//(0*x)", .divByZero),
  (inXYZ "leadMonomial(x-x)", .algebra "zero polynomial has no leading monomial"),
  (inXYZ "m2MonomialQuotient(x,y)", .algebra "monomial does not divide the numerator"),
  (inXYZ "m2MonomialLCM(x+y,x)", .algebra "expected a nonzero single-term polynomial"),
  (inXYZ "m2Monomial(R,{1,2})", .algebra "monomial exponent vector has the wrong dimension"),
  (inXYZ "m2Monomial(R,{1,-2,0})", .algebra "negative monomial exponent"),
  (inXYZ "m2Monomial(R,{1,1/2,0})", .algebra "expected integer monomial exponents"),
  (inXYZ "leadTerm()", .arity 1 0),
  (inXYZ "leadTerm(x,y)", .arity 1 2),
  (inXYZ "promote(x)", .arity 2 1),
  (inXYZ "m2MonomialDivides(x,y,z)", .arity 2 3),
  ("QQ=7", .protectedSymbol "QQ"),
  ("QQ[true]", .protectedSymbol "true"),
  ("QQ[leadTerm]", .protectedSymbol "leadTerm"),
  ("R=QQ[x];p=x;S=QQ[x];p+x", .algebra "polynomials belong to different rings")
]

/-- Rejection boundaries. Native validity is tested separately where claimed. -/
def unsupported : List String := [
  "QQ[x,x]", "QQ[x_0..x_2]", "QQ[x,MonomialOrder=>Lex]", "ZZ[x]",
  "R=QQ[x];x/x", "R=QQ[x];1/x", "R=QQ[x];x^(-1)",
  "R=QQ[x,y];(x^2+y)//(x+y)", "R=QQ[x];ideal(x)==ideal(2*x)",
  "R=QQ[x];R==R", "coefficientRing QQ[x]==QQ",
  "R=QQ[x,y];old=x+y;QQ[old]", "x=2;QQ[x,y]",
  "R=QQ[x];degree(0*x)", "R=QQ[x];ideal()"
]
end Macaulean.M2.PolynomialCases
