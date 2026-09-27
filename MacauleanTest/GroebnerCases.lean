import Macaulean.Interpreter.Run

/-! Systems exercising new critical pairs, zero/duplicate inputs, units,
rational coefficients, nonreduced ideals, input order, and zero variables. -/
namespace Macaulean.M2.GroebnerCases
structure Case where
  name : String
  variables : String
  generators : String
  deriving Repr

def systems : List Case := [
  ⟨"zero ideal", "px,py", "promote(0,rr)"⟩,
  ⟨"principal", "px,py", "px^2-py"⟩,
  ⟨"duplicate and zero", "px,py", "0*px,2*px^2-2*py,px^2-py"⟩,
  ⟨"constant unit", "px,py", "promote(2,rr)"⟩,
  ⟨"unit discovered by reduction", "px,py", "px,1-px"⟩,
  ⟨"nonhomogeneous new pairs", "px,py", "px^2-py,px*py-1"⟩,
  ⟨"already monomial", "px,py", "px^2,px*py,py^2"⟩,
  ⟨"symmetric quotient", "px,py", "px*py-1,py^2-1"⟩,
  ⟨"circle diagonal", "px,py", "px^2+py^2-1,px-py"⟩,
  ⟨"rational coefficients", "px,py", "px/2+py/3,px-py"⟩,
  ⟨"idempotents", "px,py", "px^2-px,py^2-py,px*py"⟩,
  ⟨"equal leading terms", "px,py", "px^2+py,px^2-py,px*py"⟩,
  ⟨"one variable gcd", "px", "px^4-1,px^3-1"⟩,
  ⟨"redundant leading ideal", "px", "px^3,px^2,px,0*px"⟩,
  ⟨"triangular three variable", "px,py,pz", "px-py,py-pz,pz^2-1"⟩,
  ⟨"cyclic three", "px,py,pz", "px+py+pz,px*py+px*pz+py*pz,px*py*pz-1"⟩,
  ⟨"reversed generators", "px,py", "px*py-1,px^2-py"⟩,
  ⟨"redundant nonmonomial", "px,py", "px^2-py,px*py-1,px*(px^2-py)"⟩,
  ⟨"constant polynomial ring", "", "promote(3,rr)"⟩,
  ⟨"zero constant polynomial ring", "", "promote(0,rr)"⟩,
  ⟨"rational nonlinear", "px,py", "px^2/2-py/3,px*py/5-1/7"⟩,
  ⟨"nonradical", "px,py", "px^2,px*py,py^3"⟩,
  ⟨"unit from nonconstant generators", "px,py", "px,px*py-1"⟩,
  ⟨"all zero repeated", "px,py", "0*px,0*py,0*px"⟩
]

def Case.setup (c : Case) : String :=
  "rr:=QQ[" ++ c.variables ++ "];ii:=ideal(" ++ c.generators ++ ");"
def Case.source (c : Case) : String := "(" ++ c.setup ++ "gb ii)"

/-- Native QQ bases may clear denominators, whereas our contract is monic.
Normalize only by the leading scalar; every exponent and remaining coefficient
is still compared exactly. No reduction or ideal-membership test is hidden here. -/
def formsFunction : String :=
  "observe:=(xs,j)->if j==#xs then {} else " ++
  "{listForm ((xs#j)/(leadCoefficient (xs#j)))}|observe(xs,j+1);"
def Case.observation (c : Case) : String :=
  "(" ++ c.setup ++ formsFunction ++ "observe((entries gens gb ii)#0,0))"
end Macaulean.M2.GroebnerCases
