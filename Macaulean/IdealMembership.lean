import Lean

open Lean Grind Elab Tactic Meta

def toGrindExpr? (x : Lean.Expr) : Option Lean.Grind.CommRing.Expr :=
  match x with
  | .bvar _ => sorry
  | .fvar _ => sorry
  | _ => sorry

elab "m2idealmem" : tactic => do
  let goal ← getMainGoal
  let target ← getMainTarget
  let some (ring,lhs,rhs) := target.eq? | throwTacticEx `m2idealmem goal "Expected an equality"
  --check if rhs is zero
  --check that ring is a ring we know how to work with
  let some targetGrindExpr := toGrindExpr? lhs | throwTacticEx `m2idealmem goal "Expected a polynomial expression"
  let targetPoly := targetGrindExpr.toPoly
  --get the polynomials for all polynomial expressions in the local context
  --send the "ideal" of the local polynomials and the target polynomial to Macaulay2
  --read the result back and try to prove the equality
