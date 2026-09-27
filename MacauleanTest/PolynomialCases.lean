import Macaulean.Interpreter.Run

/-! Explicit expected values, independent of both interpreters. Polynomials are
observed by native `listForm`: nested exponent lists and exact rational values. -/
namespace Macaulean.M2.PolynomialCases

def zz (xs : List Int) : Value := .list (xs.map Value.zz)
def form (ts : List (List Int × Rat)) : Value :=
  .list (ts.map fun (powers,c) => .sequence [zz powers,.qq c])
def overXY (s : String) : String := "(rr:=QQ[pgx,pgy];" ++ s ++ ")"

def successes : List (String × Value) := [
  ("numgens (QQ[])", .zz 0),
  ("numgens (QQ[pgx,pgy])", .zz 2),
  ("(local pgx;rr:=QQ[pgx];numgens rr)", .zz 0),
  ("(pgx:=null;rr:=QQ[pgx];numgens rr)", .zz 0),
  ("(rr:=QQ[pgx];ss:=QQ[pgx];rr==ss)", .bool false),
  ("(rr:=QQ[pgx];ss:=QQ[pgx];ring pgx==ss)", .bool true),
  ("(rr:=QQ[pgx];old:=pgx;ss:=QQ[old];{ring old==rr,ring pgx==ss})",
    .list [.bool true,.bool true]),
  (overXY "listForm pgx", form [([1,0],1)]),
  (overXY "listForm pgy", form [([0,1],1)]),
  (overXY "listForm (pgx+pgy)^2", form [([2,0],1),([1,1],2),([0,2],1)]),
  (overXY "listForm ((pgx+pgy)^2-pgx^2-2*pgx*pgy-pgy^2)", form []),
  (overXY "listForm ((2/3)*pgx^2*pgy-4*pgy+1)", form [([2,1],mkRat 2 3),([0,1],-4),([0,0],1)]),
  (overXY "listForm (-pgx+pgy)", form [([1,0],-1),([0,1],1)]),
  (overXY "listForm (pgx/2+pgy/3)", form [([1,0],mkRat 1 2),([0,1],mkRat 1 3)]),
  (overXY "listForm (0*pgx)", form []),
  (overXY "listForm (0_rr)", form []),
  (overXY "listForm (1_rr)", form [([0,0],1)]),
  (overXY "listForm promote(2/3,rr)", form [([0,0],mkRat 2 3)]),
  (overXY "listForm (pgx^0)", form [([0,0],1)]),
  (overXY "listForm ((2_rr)^(-2))", form [([0,0],mkRat 1 4)]),
  -- M2's polynomial inverse uses 0 for the inverse of the zero polynomial;
  -- this must not be confused with its scalar division-by-zero error.
  (overXY "listForm ((0_rr)^(-1))", form []),
  (overXY "listForm ((0_rr)^(-2))", form []),
  (overXY "listForm ((0_rr)^0)", form [([0,0],1)]),
  (overXY "leadCoefficient ((2/3)*pgx^2*pgy-pgy)", .qq (mkRat 2 3)),
  (overXY "leadCoefficient (0*pgx)", .qq 0),
  (overXY "listForm leadMonomial (2*pgx*pgy+pgy^2+1)", form [([1,1],1)]),
  (overXY "listForm leadTerm (2*pgx*pgy+pgy^2+1)", form [([1,1],2)]),
  (overXY "listForm leadTerm (0*pgx)", form []),
  (overXY "exponents (pgx^2*pgy+pgx+pgy+1)", .list [zz [2,1],zz [1,0],zz [0,1],zz [0,0]]),
  (overXY "exponents (0*pgx)", .list []),
  (overXY "size (pgx^2*pgy+pgx+pgy+1)", .zz 4),
  (overXY "#(terms (pgx^2*pgy+pgx+pgy+1))", .zz 4),
  (overXY "#(gens rr)", .zz 2),
  (overXY "listForm (rr_0)", form [([1,0],1)]),
  (overXY "listForm ((gens rr)#1)", form [([0,1],1)]),
  (overXY "numgens ideal(pgx,pgy,0)", .zz 3),
  (overXY "ring ideal(pgx,pgy)==rr", .bool true),
  (overXY "listForm ((gens ideal(pgx,pgy))_(0,1))", form [([0,1],1)]),
  (overXY "#(flatten entries gens ideal(pgx,pgy))", .zz 2),
  (overXY "listForm ((flatten entries gens ideal(pgx,2/3))#1)", form [([0,0],mkRat 2 3)]),
  (overXY "{pgx-pgx==0,0==pgx-pgx,pgx!=0,pgx==pgy}", .list [.bool true,.bool true,.bool true,.bool false]),
  (overXY "{pgx,pgy}=={pgx+0,pgy*1}", .bool true),
  (overXY "listForm (if pgx==0 then 1_rr else pgx)", form [([1,0],1)]),
  (overXY "f:=q->q^2;listForm f(pgx+pgy)", form [([2,0],1),([1,1],2),([0,2],1)]),
  (overXY "c:=1/3;f:=q->c*q;c=2/3;listForm f pgx", form [([1,0],mkRat 2 3)]),
  ("(rr:=QQ[local qx];numgens rr)", .zz 1),
  ("(rr:=QQ[local qx];listForm qx)", form [([1],1)]),
  ("(rr:=QQ[];listForm (3_rr))", form [([],3)])
]

/-- Both implementations must raise a runtime error, not accidentally agree
because the string parser rejected a valid program. -/
def errors : List String := [
  overXY "pgx/(0_rr)",
  overXY "pgx/0",
  -- Brackets bind below application: these apply numgens to QQ first.
  "numgens QQ[]", "numgens QQ[pgx,pgy]",
  overXY "leadMonomial (0*pgx)",
  "(rr:=QQ[pgx];old:=pgx;ss:=QQ[pgx];old+pgx)",
  "(rr:=QQ[pgx];old:=pgx;ss:=QQ[pgx];old*pgx)",
  "(rr:=QQ[pgx];old:=pgx;ss:=QQ[pgx];ideal(old,pgx))",
  overXY "(gens ideal(pgx))_(0,9)",
  overXY "rr_9"
]

/-- Valid native language outside this restricted polynomial fragment; not
misclassified as malformed syntax or evidence of native/interpreter agreement. -/
def unsupported : List String := [
  "ZZ[pgx]", "QQ[7]", "QQ[pgx,pgx]", "QQ[pgx][pgy]",
  "ideal()", "ideal {}", "ideal 0", overXY "pgx/pgy"
]

def invalidSyntax : List String := [
  "QQ[", "QQ[x", "QQ[x}", "QQ[x;y]", "QQ[x,,", "R_", "R_(0,"
]
end Macaulean.M2.PolynomialCases
