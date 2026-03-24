/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Reify
import Macaulean.Grind.AlgPoly.Denote
import Macaulean.Grind.Algebra.Instances
import Lean.Elab.Tactic.Basic

/-!
# algebra_norm tactic

Verifies polynomial identities in algebras with two-level normalization.

Currently: reifies both sides, normalizes at the meta level, compares,
and closes with sorry. Future: constructs proof terms via denote theorems.
-/

open Lean Meta Elab Tactic

namespace Macaulean.AlgPoly.Tactic

/-- Walk an expression looking for `Lean.Grind.algebraMap` and extract R. -/
private partial def findR? (e : Expr) : Option Expr :=
  if e.isApp then
    let fn := e.getAppFn
    if fn.isConst && fn.constName! == ``Lean.Grind.algebraMap then
      let args := e.getAppArgs
      if args.size > 0 then some args[0]!
      else findR? e.appFn! |>.orElse fun _ => findR? e.appArg!
    else
      findR? e.appFn! |>.orElse fun _ => findR? e.appArg!
  else match e with
  | .lam _ d b _ => findR? d |>.orElse fun _ => findR? b
  | .forallE _ d b _ => findR? d |>.orElse fun _ => findR? b
  | _ => none

/--
Convert a reified AlgExpr (as Lean Expr) to an AlgPoly Int value,
by evaluating the meta-level expression. This only works when C = Int
(the base case). For towers, we'd need recursive evaluation.
-/
private partial def evalAlgExprToAlgPoly (e : Expr) : MetaM (AlgPoly Int) := do
  match_expr e with
  | AlgExpr.coeff _ r =>
    -- r should be an Int literal
    let r ← whnf r
    match r with
    | .lit (.natVal n) => return .coeff (Int.ofNat n)
    | .app (.app (.const ``Int.negSucc _) _) n =>
      let some k ← evalNat? n | return .coeff 0
      return .coeff (Int.negSucc k)
    | _ => return .coeff 0 -- fallback
  | AlgExpr.var _ i =>
    let some idx ← evalNat? i | return .coeff (0 : Int)
    return AlgPoly.ofVar (C := Int) idx
  | AlgExpr.add _ a b =>
    let pa ← evalAlgExprToAlgPoly a
    let pb ← evalAlgExprToAlgPoly b
    return pa.combine pb
  | AlgExpr.mul _ a b =>
    let pa ← evalAlgExprToAlgPoly a
    let pb ← evalAlgExprToAlgPoly b
    return pa.mul pb
  | AlgExpr.neg _ a =>
    let pa ← evalAlgExprToAlgPoly a
    return pa.neg
  | AlgExpr.sub _ a b =>
    let pa ← evalAlgExprToAlgPoly a
    let pb ← evalAlgExprToAlgPoly b
    return pa.sub pb
  | AlgExpr.pow _ a k =>
    let pa ← evalAlgExprToAlgPoly a
    let some kv ← evalNat? k | return .coeff 0
    return pa.pow kv
  | _ => return .coeff 0
where
  evalNat? (e : Expr) : MetaM (Option Nat) := do
    let e ← whnf e
    match e with
    | .lit (.natVal n) => return some n
    | _ => return none

/-- The core tactic. -/
def algebraNormCore (mvarId : MVarId) : MetaM (List MVarId) := do
  mvarId.withContext do
    let target ← mvarId.getType
    let some (_A, lhs, rhs) := target.eq?
      | throwError "algebra_norm: goal must be an equality"

    let some R := findR? target
      | throwError "algebra_norm: no algebraMap found in goal"

    let A ← inferType lhs

    let some rctx ← Reify.mkRContext? R A
      | throwError "algebra_norm: failed to synthesize Algebra {R} {A}"

    -- Reify both sides with shared variable state
    let (lhsExpr, midState) ← (Reify.reify lhs).run rctx |>.run {}
    let (rhsExpr, finalState) ← (Reify.reify rhs).run rctx |>.run midState

    -- Log reification results
    let numVars := finalState.vars.size
    logInfo m!"algebra_norm: reified with {numVars} A-variables"

    -- Evaluate AlgExpr → AlgPoly at meta level
    let lhsPoly ← evalAlgExprToAlgPoly lhsExpr
    let rhsPoly ← evalAlgExprToAlgPoly rhsExpr

    -- Compare normalized forms
    if lhsPoly.beq rhsPoly then
      logInfo m!"algebra_norm: normalized polynomials are EQUAL ✓"
      -- Close goal (with sorry for now — proof term construction is next)
      let proof ← mkSorry (← mvarId.getType) false
      mvarId.assign proof
      return []
    else
      -- Log the difference for debugging
      throwError "algebra_norm: normalized polynomials differ — identity does not hold\nLHS poly: {repr lhsPoly}\nRHS poly: {repr rhsPoly}"

elab "algebra_norm" : tactic => do
  let mvarId ← getMainGoal
  let remaining ← algebraNormCore mvarId
  replaceMainGoal remaining

end Macaulean.AlgPoly.Tactic
