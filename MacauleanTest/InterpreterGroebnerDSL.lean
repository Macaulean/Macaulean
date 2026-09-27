import Macaulean.Interpreter.DSL

/-!
# A Groebner-basis notebook, written directly in the M2 DSL

The `#guard_msgs` wrappers are test assertions, not syntax required by a user.
All algorithms run in Lean; this worksheet does not start a Macaulay2 process.
-/
namespace GroebnerWorksheet
open M2

#guard_msgs in
R = QQ[x,y];
#guard_msgs in
I = ideal(x^2-y,x*y-1);
#guard_msgs in
G = gb I;

/-- info: o4 = GroebnerBasis[3 generators] : GroebnerBasis -/
#guard_msgs in
G

/-- info: o5 = matrix{{y^2 - x, x*y - 1, x^2 - y}} : Matrix -/
#guard_msgs in
gens G

/-- info: o6 = 3 : ZZ -/
#guard_msgs in
numgens G

example : (2 : Nat) + 2 = 4 := rfl

/-- info: o7 = true : Boolean -/
#guard_msgs in
ring G === R

/-- info: o8 = 0 : QQ[x, y] -/
#guard_msgs in
(x^3-1)%G

/-- info: o9 = 1 : QQ[x, y] -/
#guard_msgs in
x^3%G

/-- info: o10 = x + 1 : QQ[x, y] -/
#guard_msgs in
(x^4+y^3)%G

/-- info: o11 = true : Boolean -/
#guard_msgs in
normalForm(x^4+y^3,G) == (x^4+y^3)%G

-- Ordered division by a list need not be canonical. The order is intentional.
/-- info: o12 = 1 : QQ[x, y] -/
#guard_msgs in
normalForm(x*y,{x*y-1,x})

/-- info: o13 = 0 : QQ[x, y] -/
#guard_msgs in
normalForm(x*y,{x,x*y-1})

/-- info: o14 = x^2 + y : QQ[x, y] -/
#guard_msgs in
normalForm(x^2+y,{})

/-- info: o15 = x^2 + y : QQ[x, y] -/
#guard_msgs in
normalForm(x^2+y,{0*x})

/-- info: o16 = -y^2 + x : QQ[x, y] -/
#guard_msgs in
sPolynomial(x^2-y,x*y-1)

/-- info: o17 = 0 : QQ[x, y] -/
#guard_msgs in
sPolynomial(x^2-y,x*y-1)%G

-- Provenance survives S-pairs, reductions, interreduction and sorting.
#guard_msgs in
C = getChangeMatrix G;

/-- info: o19 = 2 : ZZ -/
#guard_msgs in
numRows C

/-- info: o20 = 3 : ZZ -/
#guard_msgs in
numColumns C

/-- info: o21 = true : Boolean -/
#guard_msgs in
gens I*C == gens G

#guard_msgs in
G2 = gb ideal(m2GeneratorList G);

/-- info: o23 = true : Boolean -/
#guard_msgs in
gens G2 == gens G

-- Duplicate leading terms do not cause every copy to be deleted.
#guard_msgs in
H = gb ideal(0*x,2*x^2-2*y,x^2-y);

/-- info: o25 = matrix{{x^2 - y}} : Matrix -/
#guard_msgs in
gens H

/-- info: o26 = 3 : ZZ -/
#guard_msgs in
numRows getChangeMatrix H

/-- info: o27 = 1 : ZZ -/
#guard_msgs in
numColumns getChangeMatrix H

/-- info: o28 = 1 : ZZ -/
#guard_msgs in
numgens gb ideal(x,x*y-1)

/-- info: o29 = 0 : QQ[x, y] -/
#guard_msgs in
(x+y)%gb ideal(x,x*y-1)

-- The zero ideal has an empty basis; its matrix dimensions are not forgotten.
#guard_msgs in
Z = gb ideal(0*x,0*y);

/-- info: o31 = 0 : ZZ -/
#guard_msgs in
numgens Z

/-- info: o32 = {{}} : List -/
#guard_msgs in
entries gens Z

/-- info: o33 = {2, 0} : List -/
#guard_msgs in
{numRows getChangeMatrix Z,numColumns getChangeMatrix Z}

/-- info: o34 = true : Boolean -/
#guard_msgs in
gens ideal(0*x,0*y)*getChangeMatrix Z == gens Z

/-- info: o35 = x + y : QQ[x, y] -/
#guard_msgs in
(x+y)%Z

-- Reusing printed variable names does not change older rings or bases.
#guard_msgs in
p = x;
#guard_msgs in
saved = G;
#guard_msgs in
S = QQ[x,y];

/-- info: o39 = 0 : QQ[x, y] -/
#guard_msgs in
(p^3-1)%saved

/-- error: polynomials belong to different rings -/
#guard_msgs in
x%saved

/-- info: o41 = true : Boolean -/
#guard_msgs in
ring p === R

/-- info: o42 = true : Boolean -/
#guard_msgs in
ring x === S

-- gb is a first-class source-language function, not special command syntax.
#guard_msgs in
runner = f -> arg -> f arg;
#guard_msgs in
runGB = runner gb;
#guard_msgs in
J = ideal(x^2-y,x*y-1);

/-- info: o46 = true : Boolean -/
#guard_msgs in
gens(runGB J) == gens(gb J)

#guard_msgs in
countBasis = numgens@@gb;

/-- info: o48 = 3 : ZZ -/
#guard_msgs in
countBasis J

#guard_msgs in
holder = {gb,gb J};

/-- info: o50 = true : Boolean -/
#guard_msgs in
gens((holder#0) J) == gens(holder#1)

/-- error: attempted to modify a protected symbol 'gb' -/
#guard_msgs in
gb = 3

/-- info: o52 = 3 : ZZ -/
#guard_msgs in
numgens(gb J)

/-- error: cannot promote Boolean to QQ[x, y] -/
#guard_msgs in
normalForm(x,{true})

/-- error: expected 2 arguments, got 3 -/
#guard_msgs in
normalForm(x,y,1)

/-- error: zero polynomial has no leading monomial -/
#guard_msgs in
sPolynomial(0*x,y)

-- A fabricated representation cannot silently produce a basis object.
/-- error: invalid basis provenance -/
#guard_msgs in
m2MakeBasis(J,{{x,{1,0}}})

/-- error: coefficient row has the wrong dimension -/
#guard_msgs in
m2MakeBasis(J,{{x^2-y,{1}}})

/-- error: basis must be monic -/
#guard_msgs in
m2MakeBasis(J,{{2*x,{1,0}}})

/-- error: matrix multiplication dimension mismatch -/
#guard_msgs in
numRows(gens J*gens J)

/-- info: o60 = 3 : ZZ -/
#guard_msgs in
numgens G

-- The zero-variable polynomial ring still has zero and unit ideals.
#guard_msgs in
K = QQ[];
#guard_msgs in
U = gb ideal(promote(2,K));

/-- info: o63 = {{1}} : List -/
#guard_msgs in
entries gens U

/-- info: o64 = true : Boolean -/
#guard_msgs in
gens ideal(promote(2,K))*getChangeMatrix U == gens U

/-- info: o65 = 0 : ZZ -/
#guard_msgs in
numgens gb ideal(promote(0,K))

#guard_msgs in
report = F -> (
  B := gb F;
  {numgens B,numColumns getChangeMatrix B});

/-- info: o67 = {3, 3} : List -/
#guard_msgs in
report J

/-- info: o68 = {true, true} : List -/
#guard_msgs in
{ring saved === R,ring(holder#1) === S}

open Lean Elab Command in
run_cmd do
  let state ← Macaulean.M2.DSL.getSession
  unless state.nextInput == 69 do throwError "Buchberger worksheet input boundaries changed"
  logInfo "BUCHBERGER_WORKSHEET_COMPLETE: 68 annotated inputs"
end GroebnerWorksheet
