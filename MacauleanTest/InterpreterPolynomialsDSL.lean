import Macaulean.Interpreter.DSL

/-!
# Polynomials in the worksheet

Open this file in Lean. The bare M2 inputs are the interface; #guard_msgs only
asserts their InfoView transcript. Every scalar, polynomial, ideal and closure here
is evaluated by the pure interpreter. No external algebra engine is imported.
-/
namespace PolynomialWorksheet
open M2

/-- info: o1 = QQ[x, y] : PolynomialRing -/
#guard_msgs in
R = QQ[x,y]

#guard_msgs in
p = (x+y)^2;

/-- info: o3 = x^2 + 2*x*y + y^2 : QQ[x, y] -/
#guard_msgs in
p

/-- info: o4 = 0 : QQ[x, y] -/
#guard_msgs in
p - x^2 - 2*x*y - y^2

/-- info: o5 = x^2 - y^2 : QQ[x, y] -/
#guard_msgs in
(x+y)*(x-y)

/-- info: o6 = (1/2)*x^2 + x*y + (1/2)*y^2 : QQ[x, y] -/
#guard_msgs in
p/2

/-- info: o7 = 3/1 : QQ -/
#guard_msgs in
leadCoefficient(3*x^2-y)

/-- info: o8 = x^2 : QQ[x, y] -/
#guard_msgs in
leadMonomial(3*x^2-y)

/-- info: o9 = 3*x^2 : QQ[x, y] -/
#guard_msgs in
leadTerm(3*x^2-y)

/-- info: o10 = {{2, 0}, {1, 1}, {0, 2}} : List -/
#guard_msgs in
exponents p

/-- info: o11 = {({2, 0}, 1/1), ({1, 1}, 2/1), ({0, 2}, 1/1)} : List -/
#guard_msgs in
listForm p

/-- info: o12 = {x^2, y} : List -/
#guard_msgs in
terms(x^2+y)

/-- info: o13 = 3 : ZZ -/
#guard_msgs in
size p

/-- info: o14 = ideal(x^2 - y, x*y - 1) : Ideal -/
#guard_msgs in
I = ideal(x^2-y,x*y-1)

/-- info: o15 = matrix{{x^2 - y, x*y - 1}} : Matrix -/
#guard_msgs in
gens I

/-- info: o16 = {{x^2 - y, x*y - 1}} : List -/
#guard_msgs in
entries gens I

/-- info: o17 = 2 : ZZ -/
#guard_msgs in
numgens I

/-- info: o18 = true : Boolean -/
#guard_msgs in
ring I == R

/-- info: o19 = true : Boolean -/
#guard_msgs in
(gens R)#0 == x

-- Rebinding p cannot alter the saved immutable polynomial.
#guard_msgs in
saved = p;
#guard_msgs in
p = p+1;

/-- info: o22 = x^2 + 2*x*y + y^2 : QQ[x, y] -/
#guard_msgs in
saved

/-- info: o23 = false : Boolean -/
#guard_msgs in
p == saved

-- The polynomial primitives are first-class callable values.
#guard_msgs in
inspect = leadCoefficient @@ leadTerm;

/-- info: o25 = 7/1 : QQ -/
#guard_msgs in
inspect(7*x-y)

/-- info: o26 = true : Boolean -/
#guard_msgs in
m2MonomialDivides(x,x^2*y)

/-- info: o27 = false : Boolean -/
#guard_msgs in
m2MonomialDivides(x^2,x*y)

/-- info: o28 = (3/2)*x*y : QQ[x, y] -/
#guard_msgs in
m2MonomialQuotient(3*x^2*y,2*x)

/-- info: o29 = x^2*y : QQ[x, y] -/
#guard_msgs in
m2MonomialLCM(2*x^2,3*x*y)

/-- info: o30 = 1 : ZZ -/
#guard_msgs in
m2MonomialCompare(x,y)

/-- info: o31 = x^2*y^3 : QQ[x, y] -/
#guard_msgs in
m2Monomial(R,{2,3})

/-- info: o32 = 0/1 : QQ -/
#guard_msgs in
leadCoefficient(x-x)

/-- info: o33 = 0 : QQ[x, y] -/
#guard_msgs in
leadTerm(x-x)

/-- info: o34 = {} : List -/
#guard_msgs in
exponents(x-x)

/-- error: zero polynomial has no leading monomial -/
#guard_msgs in
leadMonomial(x-x)

/-- info: o36 = x^2 + 2*x*y + y^2 + 1 : QQ[x, y] -/
#guard_msgs in
p

-- Fraction fields are deliberately not silently treated as polynomial division.
/-- error: polynomial division by a polynomial requires the fraction-field extension -/
#guard_msgs in
x/x

/-- info: o38 = false : Boolean -/
#guard_msgs in
false and (x/x == 1)

-- Constructing another ring does not migrate old polynomials to it.
/-- info: o39 = QQ[x] : PolynomialRing -/
#guard_msgs in
R = QQ[x]

/-- info: o40 = false : Boolean -/
#guard_msgs in
ring saved == R

/-- info: o41 = x^2 + 2*x*y + y^2 : QQ[x, y] -/
#guard_msgs in
saved

/-- error: polynomials belong to different rings -/
#guard_msgs in
saved + x

/-- info: o43 = 2 : ZZ -/
#guard_msgs in
numgens ring saved

/-- info: o44 = true : Boolean -/
#guard_msgs in
ring x == R

#guard_msgs in
hold = x;
#guard_msgs in
T = QQ[x];

-- Even identical displayed rings have separate identities.
/-- info: o47 = false : Boolean -/
#guard_msgs in
ring hold == T

/-- info: o48 = x^2 : QQ[x] -/
#guard_msgs in
hold^2

/-- error: polynomials belong to different rings -/
#guard_msgs in
hold+x

#guard_msgs in
maker = a -> p -> p+a;
#guard_msgs in
shift = maker hold;

/-- info: o52 = 2*x : QQ[x] -/
#guard_msgs in
shift hold

-- Quoted ring names publish globals, not a same-spelled lexical parameter.
#guard_msgs in
bindTest = (x) -> (V=QQ[x];x);

/-- info: o54 = 17 : ZZ -/
#guard_msgs in
bindTest 17

/-- info: o55 = true : Boolean -/
#guard_msgs in
ring hold == R

/-- info: o56 = {} : List -/
#guard_msgs in
gens QQ[]

#guard_msgs in
R = QQ[
  x, -- UTF-8 in original source: λ, 中文
  y];

/-- info: o58 = x^3 - 3*x^2*y + 3*x*y^2 - y^3 : QQ[x, y] -/
#guard_msgs in
(x-y)^3

/-- info: o59 = true : Boolean -/
#guard_msgs in
(x-y)^3 == x^3-3*x^2*y+3*x*y^2-y^3

/-- error: attempted to modify a protected symbol 'true' -/
#guard_msgs in
QQ[true]

/-- info: o61 = true : Boolean -/
#guard_msgs in
ring x == R

-- Ordinary Lean still has its own names and syntax.
def x : Nat := 99
example : x = 99 := rfl

end PolynomialWorksheet

namespace PolynomialReaderTests
open Lean Elab Command

run_cmd do
  for source in #["QQ[x,y]", "QQ[]", "(QQ)[x]", "gens QQ[x,y]", "f=()->QQ[x]",
      "R=QQ[\n x, -- λ 中文\n y];", "(R=QQ[x];x+1)", "(QQ)[a,b][c]"] do
    let .ok syntax := Parser.runParserCategory (← getEnv) `m2 source
      | throwError "category rejected polynomial source {source}"
    let .ok (actual, silent) := Macaulean.M2.DSL.lowerInput ⟨syntax⟩
      | throwError "lowering failed for {source}"
    let .ok expected := Macaulean.M2.parse source
      | throwError "string parser rejected {source}"
    unless actual == expected do throwError "parser AST disagreement for {source}"
    unless silent == source.endsWith ";" do throwError "terminator lost for {source}"
    let rendered ← liftCoreM <| PrettyPrinter.ppCategory `m2 syntax
    let .ok reparsed := Parser.runParserCategory (← getEnv) `m2 rendered.pretty
      | throwError "formatter output no longer parses"
    let .ok (again, sameSilent) := Macaulean.M2.DSL.lowerInput ⟨reparsed⟩
      | throwError "formatted syntax does not lower"
    unless again == actual && sameSilent == silent do throwError "formatting changed semantics"
    unless Macaulean.M2.parse actual.toM2String == .ok actual do
      throwError "AST printing changed polynomial syntax {source}"

run_cmd do
  let source := "QQ[ -- λ 中文\n x,y]"
  let .ok syntax := Parser.runParserCategory (← getEnv) `m2 source
    | throwError "source-location example did not parse"
  let body := syntax[0][0]
  unless body.getKind == `Macaulean.M2.DSL.polyRing do throwError "polynomial syntax is opaque"
  for (atom, expected) in #[(body[1], "["), (body[3], "]"), (body[2][0][0], "x"), (body[2][2][0], "y")] do
    let some begin := atom.getPos? | throwError "missing source position"
    let some finish := atom.getTailPos? | throwError "missing end position"
    unless String.Pos.Raw.extract source begin finish == expected do
      throwError "wrong original UTF-8 byte range for {expected}"
  if (Parser.runParserCategory (← getEnv) `command "QQ[x,y]").isOk then
    throwError "scoped language activation escaped its namespace"
end PolynomialReaderTests
