import Macaulean.CAS.Strategy

open Lean Elab Tactic Meta

namespace Macaulean.CAS

/-! # The `cas` Tactic

Recursive dispatch loop: matches goals to registered strategies,
recurses on subgoals with shared context and cache.
-/

structure CASLoopState where
  attempted : Std.HashSet (UInt64)   -- hash of (goal id, strategy name) pairs
  fuel : Nat

private def goalStrategyKey (goal : MVarId) (strategy : Name) : UInt64 :=
  hash (goal.name, strategy)

/-- Try each strategy on the goal, skipping already-attempted pairs. -/
private def tryStrategies (ctx : CASContext) (state : IO.Ref CASLoopState)
    (strategies : Array CASStrategyEntry) (goal : MVarId) :
    TacticM (Option (List MVarId)) := do
  for strategy in strategies do
    let key := goalStrategyKey goal strategy.name
    let s ← state.get
    if s.attempted.contains key then continue
    state.modify fun s => { s with attempted := s.attempted.insert key }
    if ← strategy.match? goal then
      let subgoals ← strategy.execute ctx goal
      return some subgoals
  return none

/-- Recursive loop: try strategies on each goal, recurse on subgoals. -/
partial def casLoop (ctx : CASContext) (state : IO.Ref CASLoopState)
    (goals : List MVarId) : TacticM (List MVarId) := do
  let strategies ← getRegisteredStrategies
  let strategies := strategies.qsort fun a b =>
    a.priority < b.priority || (a.priority == b.priority && a.name.toString < b.name.toString)
  let mut remaining := []
  for goal in goals do
    if ← goal.isAssigned then continue
    let s ← state.get
    if s.fuel == 0 then
      remaining := remaining ++ [goal]
      continue
    match ← tryStrategies ctx state strategies goal with
    | some subgoals =>
        state.modify fun s => { s with fuel := s.fuel - 1 }
        remaining := remaining ++ (← casLoop ctx state subgoals)
    | none =>
        remaining := remaining ++ [goal]
  return remaining

elab "cas" : tactic => do
  let goal ← getMainGoal
  let ctx ← mkCASContext
  let state ← IO.mkRef ({ attempted := {}, fuel := 100 } : CASLoopState)
  try
    let remaining ← casLoop ctx state [goal]
    -- Only replace goals if the original goal wasn't already closed by a strategy
    if ← goal.isAssigned then
      -- Strategy closed the goal directly (via setGoals/evalTactic)
      -- Just set whatever subgoals remain
      setGoals remaining
    else
      replaceMainGoal remaining
  finally
    ctx.cleanup

end Macaulean.CAS
