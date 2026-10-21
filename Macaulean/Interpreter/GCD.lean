import Macaulean.Interpreter.Runtime

/-!
# Univariate QQ GCD, executed from M2 source

`compute` selects an evaluation-depth budget from the normalized input degrees.
`GCD.Execution.compute_total` proves that every accepted input succeeds
within this budget and returns a monic-or-zero GCD, executing the actual source.
The proof module is separate to avoid an import cycle.
-/
namespace Macaulean.M2.GCD
open Polynomials

/-- Natural degree, with zero assigned degree zero. Only used after validating
univariate input; take the maximum rather than trusting raw term order. -/
def degree (p : Raw) : Nat :=
  p.foldl (fun d t => max d t.2.sum) 0

/-- Depth allowance for the source-language GCD and normal-form calls.
Sufficiency is proved in `GCD.Execution.input_fuel_sufficient`. -/
def fuelForDegree (d : Nat) : Nat := 128 * (d + 4)

def fuel (p q : Raw) : Nat := fuelForDegree (max (degree p) (degree q))

theorem fuelForDegree_pos (d : Nat) : 0 < fuelForDegree d := by
  unfold fuelForDegree
  omega

theorem fuelForDegree_mono {d e : Nat} (h : d ≤ e) :
    fuelForDegree d ≤ fuelForDegree e := by
  unfold fuelForDegree
  omega

theorem fuel_comm (p q : Raw) : fuel p q = fuel q p := by
  simp only [fuel, Nat.max_comm]

/-- Validate inputs, derive the budget, and run the actual checked-in M2 source.
This API does not use a native M2 process or a second Lean GCD implementation. -/
def compute (f g : Value) : Except Error Value := do
  let (r,p,q) ← gcdInputs (.sequence [f,g])
  let (result,_) ← Runtime.finish (Runtime.call (fuel p q)
    (.algebra (.library "gcd"))
    (.sequence [.algebra (.poly r p), .algebra (.poly r q)]) {})
  return result

end Macaulean.M2.GCD
