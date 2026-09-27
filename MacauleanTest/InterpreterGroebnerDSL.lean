import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Check

/-!
# A polynomial notebook, with Buchberger running in the language

The `#guard_msgs` wrappers assert the transcript; users write only `open M2`
and the bare inputs. In particular, `gb` is the source program in Buchberger.m2,
not a call to the native Macaulay2 engine.
-/
namespace M2GroebnerWorksheet
open M2
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

#guard_msgs in
R = QQ[x,y];
#guard_msgs in
p = x^2-y;
/-- info: o3 = x^2 - y : QQ[x, y] -/
#guard_msgs in
p
#guard_msgs in
q = x*y-1;
#guard_msgs in
I = ideal(p,q);

-- This example needs a new S-polynomial, not just sorting the input.
/-- info: o6 = GroebnerBasis[3 generators over QQ[x, y]] : GroebnerBasis -/
#guard_msgs in
G = gb I
/-- info: o7 = matrix {{y^2 - x, x*y - 1, x^2 - y}} : Matrix -/
#guard_msgs in
gens G

/-- info: o8 = 0 : QQ[x, y] -/
#guard_msgs in
p%G
/-- info: o9 = 0 : QQ[x, y] -/
#guard_msgs in
q%G
/-- info: o10 = 0 : QQ[x, y] -/
#guard_msgs in
(x^3-1)%G
/-- info: o11 = x + y : QQ[x, y] -/
#guard_msgs in
(x+y)%G

-- The algorithm retained expressions in the ORIGINAL generators.
/-- info: o12 = true : Boolean -/
#guard_msgs in
gens I * getChangeMatrix G == gens G
/-- info: o13 = 2 : ZZ -/
#guard_msgs in
#(entries getChangeMatrix G)
/-- info: o14 = 3 : ZZ -/
#guard_msgs in
#((entries getChangeMatrix G)#0)

-- Zero, redundant, repeated, and nonmonic inputs do not corrupt cleanup.
/-- info: o15 = matrix {{y^2 - x, x*y - 1, x^2 - y}} : Matrix -/
#guard_msgs in
gens gb ideal(0_R,2*p,p,q)
/-- info: o16 = matrix {{}} : Matrix -/
#guard_msgs in
gens gb ideal(0_R)
/-- info: o17 = matrix {{1}} : Matrix -/
#guard_msgs in
gens gb ideal(x,1-x)
#guard_msgs in
fractional = gb ideal(x/2+y/3,x-y);
/-- info: o19 = matrix {{y, x}} : Matrix -/
#guard_msgs in
gens fractional

-- Reusing printed variable names creates a DIFFERENT ring, not type confusion.
#guard_msgs in
oldX = x;
#guard_msgs in
S = QQ[x,y];
/-- info: o22 = true : Boolean -/
#guard_msgs in
ring oldX == R
/-- info: o23 = true : Boolean -/
#guard_msgs in
ring x == S
/-- error: polynomials belong to different rings -/
#guard_msgs in
oldX+x
/-- info: o25 = 0 : QQ[x, y] -/
#guard_msgs in
(oldX^3-1)%G
/-- info: o26 = true : Boolean -/
#guard_msgs in
S_0 == x

-- Rings and bases may escape functions without losing their lexical symbols.
#guard_msgs in
makeExample = () -> (T := QQ[local z]; {T,z,gb ideal(z^2-1)});
#guard_msgs in
data = makeExample();
/-- info: o29 = matrix {{z^2 - 1}} : Matrix -/
#guard_msgs in
gens(data#2)

-- Native Lean declarations can still be interleaved with the notebook.
example : (7 : Nat) + 5 = 12 := rfl

-- Explicit resource exhaustion is an error, not a partial GroebnerBasis.
set_option m2.maxDepth 2
/-- error: M2 evaluation depth exhausted -/
#guard_msgs in
gb ideal(x^2-y,x*y-1)
set_option m2.maxDepth 4096
/-- info: o31 = matrix {{y^2 - x, x*y - 1, x^2 - y}} : Matrix -/
#guard_msgs in
gens G

-- Multiline ring specifications retain their original syntax/source positions.
#guard_msgs in
U = QQ[
  local a,
  local b
];
/-- info: o33 = a^2 + 2*a*b + b^2 : QQ[a, b] -/
#guard_msgs in
(a+b)^2
/-- info: o34 = (2/3)*a^2*b - 4*b + 1 : QQ[a, b] -/
#guard_msgs in
(2/3)*a^2*b-4*b+1
/-- info: o35 = {({2, 1}, 2/3), ({0, 1}, -4/1), ({0, 0}, 1/1)} : List -/
#guard_msgs in
listForm ((2/3)*a^2*b-4*b+1)

-- A forged change matrix cannot create a basis result with false provenance.
/-- error: invalid change-of-basis identity -/
#guard_msgs in
m2MakeBasis(ideal a,{{b,{1_U}}})
/-- info: o37 = a : QQ[a, b] -/
#guard_msgs in
a
end M2GroebnerWorksheet

namespace M2GroebnerSyntaxTests
open Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

run_cmd do
  for source in #["QQ[]", "QQ[x,y]", "QQ[local x,local y]", "QQ[(x,y)]",
      "R=QQ[x,y];", "R_0", "0_R", "(gens gb I)_(0,1)",
      "QQ[\nlocal x, -- λ, 中文\nlocal y\n]", "gens gb ideal(x^2-y,x*y-1)"] do
    let .ok expected := Macaulean.M2.parse source | throwError "string parser failed: {source}"
    let .ok stx := Parser.runParserCategory (← getEnv) `m2 source
      | throwError "category parser failed: {source}"
    let .ok (actual,_) := Macaulean.M2.DSL.lowerInput ⟨stx⟩
      | throwError "lowering failed: {source}"
    unless actual == expected do throwError "different ASTs: {source}"
    let .ok printed := Macaulean.M2.parse actual.toM2String
      | throwError "AST printer failed: {actual.toM2String}"
    unless printed == actual do throwError "AST roundtrip changed the polynomial program"

run_cmd do
  let source := "QQ[local x, -- λ, 中文\nlocal y]"
  let .ok stx := Parser.runParserCategory (← getEnv) `m2 source
    | throwError "ring category parser failed"
  let body := stx[0][0]
  unless body.getKind == `Macaulean.M2.DSL.ringNew do throwError "ring syntax is opaque"
  for (index,text) in #[(1,"["),(3,"]")] do
    let some a := body[index].getPos? | throwError "missing bracket position"
    let some b := body[index].getTailPos? | throwError "missing bracket end position"
    unless String.Pos.Raw.extract source a b == text do throwError "corrupt UTF-8 bracket range"
  if (Parser.runParserCategory (← getEnv) `command "QQ[x,y]").isOk then
    throwError "bare M2 leaked outside its opened scope"
end M2GroebnerSyntaxTests
