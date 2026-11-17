import Macaulean.Interpreter.GCD
import Macaulean.Interpreter.Run

namespace Macaulean.M2.GCDTests

/-- Explicit monic answers, independent of both GCD implementations. -/
def cases : List (String × String × String) := [
  ("0*x", "0*x", "0*x"),
  ("0*x", "2*x^2+4*x+2", "x^2+2*x+1"),
  ("-3*x^2+3", "0*x", "x^2-1"),
  ("promote(2,R)", "promote(-3,R)", "promote(1,R)"),
  ("x", "promote(2,R)", "promote(1,R)"),
  ("x^4-1", "x^3-1", "x-1"),
  ("x^3-1", "x^4-1", "x-1"),
  ("x^2+1", "x+1", "promote(1,R)"),
  ("x^3", "x^2", "x^2"),
  ("2*x+2", "-3*x-3", "x+1"),
  ("(x-1)^4*(x+2)", "(x-1)^2*(x+3)", "(x-1)^2"),
  ("(x/2+1/3)*(x-2)", "(x/3+2/9)*(x+5)", "x+2/3"),
  ("x^5+3*x^3+2*x", "x^4+2*x^2+1", "x^2+1"),
  ("x^6+5*x^4+6*x^2+1", "x^5+4*x^3+3*x", "promote(1,R)")
]

def poly (p : Polynomials.Raw) : Value :=
  .algebra (.poly ⟨0,["x"]⟩ p)

end Macaulean.M2.GCDTests
