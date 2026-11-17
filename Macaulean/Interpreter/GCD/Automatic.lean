import Macaulean.Interpreter.GCD

namespace Macaulean.M2.GCD

/-- Execute the checked-in source with a fresh degree-derived depth allowance,
while retaining the caller's runtime state and ring identities. -/
def callWithBudget (arg : Value) (s : Runtime.State) :
    Except Runtime.Signal (Value × Runtime.State) := do
  let (r,p,q) ← Runtime.liftResult (Polynomials.gcdInputs arg)
  Runtime.call (fuel p q) (.algebra (.library "gcd"))
    (.sequence [.algebra (.poly r p),.algebra (.poly r q)]) s

/-- Recognition is by function value, so aliases, higher-order calls and nested
closures receive the same budget. The bounded subcall uses no handler. -/
def handler : Runtime.CallHandler := fun fn arg s =>
  match fn with
  | .algebra (.library "gcd") => some (callWithBudget arg s)
  | _ => none

end Macaulean.M2.GCD
