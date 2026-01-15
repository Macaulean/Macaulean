import Lean

open Lean Grind Elab Tactic Meta

structure VariableState where
  varTable : FVarIdMap CommRing.Var
  nextVar : CommRing.Var

def VariableState.mapVariable (state : VariableState) (var : FVarId) :
  CommRing.Var × VariableState :=
  let (optVar, newTable) := state.varTable.getThenInsertIfNew? var state.nextVar
  match optVar with
  | .some var => (var, state)
  | .none => (state.nextVar, {
      state with
        varTable := newTable
        nextVar := state.nextVar + 1})

def VariableState.empty : VariableState := {
  varTable := .empty
  nextVar := .zero
}

--inspired by Grind.Arith.CommRing.reify?
partial def toCommRingExpr?
  (x : Lean.Expr)
  : StateT VariableState MetaM (Option Lean.Grind.CommRing.Expr) := do
  match_expr x with
  --TODO: figure out what we need to be careful about with types
  | HAdd.hAdd _ _ _ _ a b =>
    pure <| .add <$> (← toCommRingExpr? a) <*> (← toCommRingExpr? b)
  | HMul.hMul _ _ _ _ a b =>
    pure <| .mul <$> (← toCommRingExpr? a) <*> (← toCommRingExpr? b)
  | HSub.hSub _ _ _ _ a b =>
    pure <| .sub <$> (← toCommRingExpr? a) <*> (← toCommRingExpr? b)
  | HPow.hPow _ _ _ _ a b =>
    pure <| .pow <$> (← toCommRingExpr? a) <*> (← getNatValue? b)
  | _ =>
    match ← getNatValue? x with
    | some k => pure <| some <| .natCast k
    | _ =>
      let .fvar varId := x | return none
      let varName ← modifyGet (
        fun varState => varState.mapVariable varId)
      pure <| some <| .var varName



-- #eval toCommRingExpr? `(x^2 + y^2 - z^2)

elab "m2idealmem" : tactic => do
  let goal ← getMainGoal
  let target ← getMainTarget
  IO.print target
  let some (ring,lhs,rhs) := target.eq? | throwTacticEx `m2idealmem goal "Expected an equality"
  --check if rhs is zero
  --check that ring is a ring we know how to work with
  let (some targetGrindExpr, vars) ← (toCommRingExpr? lhs).run .empty | throwTacticEx `m2idealmem goal "Expected a polynomial expression"
  let targetPoly := targetGrindExpr.toPoly
  IO.print <| repr targetPoly
  --get the polynomials for all polynomial expressions in the local context
  --send the "ideal" of the local polynomials and the target polynomial to Macaulay2
  --read the result back and try to prove the equality

example : (x + y = 0) → (x + y)^2 = 0 := by
  intro
  m2idealmem
