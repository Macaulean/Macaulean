/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Expr
import Macaulean.Grind.Algebra.Defs
import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.Meta.SynthInstance

/-!
# Reification: Lean Expr → AlgExpr C

Walks a Lean expression of type `A` (where `Algebra R A` exists) and builds
an `AlgExpr C` term, plus a variable context.

## Classification

- `algebraMap R A r` → `AlgExpr.coeff r`
- Ring operations → structural (`add`, `mul`, `sub`, `neg`, `pow`)
- Everything else → `AlgExpr.var i` (fresh variable index)
-/

open Lean Meta

namespace Macaulean.AlgPoly.Reify

/-- State for reification. -/
structure RState where
  /-- A-variables encountered, indexed by Var. -/
  vars : Array Expr := #[]
  /-- Deduplication map: Lean Expr → Var index. -/
  varMap : Std.HashMap Expr Nat := {}

/-- Context for reification: the algebra structure being reified against. -/
structure RContext where
  R : Expr
  A : Expr
  uR : Level
  uA : Level
  /-- The algebraMap function, fully applied to instances:
      `@Lean.Grind.algebraMap R A csR sA algInst` -/
  algebraMapFn : Expr

abbrev ReifyM := ReaderT RContext (StateT RState MetaM)

/-- Assign a variable index to an A-expression, deduplicating. -/
private def mkVar (e : Expr) : ReifyM Nat := do
  let s ← getThe RState
  match s.varMap[e]? with
  | some idx => return idx
  | none =>
    let idx := s.vars.size
    modifyThe RState fun s => { s with
      vars := s.vars.push e
      varMap := s.varMap.insert e idx }
    return idx

-- AlgExpr constructors as Lean Expr builders

private def mkE (n : Name) (args : Array Expr) : ReifyM Expr := do
  let ctx ← readThe RContext
  return mkAppN (mkConst n [ctx.uR]) (#[ctx.R] ++ args)

private def mkCoeffE (r : Expr) : ReifyM Expr := mkE ``AlgExpr.coeff #[r]
private def mkVarE (i : Nat) : ReifyM Expr := mkE ``AlgExpr.var #[mkRawNatLit i]
private def mkAddE (a b : Expr) : ReifyM Expr := mkE ``AlgExpr.add #[a, b]
private def mkMulE (a b : Expr) : ReifyM Expr := mkE ``AlgExpr.mul #[a, b]
private def mkSubE (a b : Expr) : ReifyM Expr := mkE ``AlgExpr.sub #[a, b]
private def mkNegE (a : Expr) : ReifyM Expr := mkE ``AlgExpr.neg #[a]
private def mkPowE (a : Expr) (k : Nat) : ReifyM Expr := mkE ``AlgExpr.pow #[a, mkRawNatLit k]

/-- Check if `e` is `algebraMapFn r` for some `r`. -/
private def isAlgebraMapApp? (e : Expr) : ReifyM (Option Expr) := do
  let ctx ← readThe RContext
  if e.isApp then
    let fn := e.appFn!
    let arg := e.appArg!
    if ← isDefEq fn ctx.algebraMapFn then
      return some arg
  return none

/-- Try to extract a Nat literal. -/
private def getNatLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => return some n
  | _ => return none

/--
Reify a Lean expression of type A into an AlgExpr term.
Returns a Lean `Expr` of type `Macaulean.AlgExpr C`.
-/
partial def reify (e : Expr) : ReifyM Expr := do
  -- 1. algebraMap R A r → coeff r
  if let some r ← isAlgebraMapApp? e then
    return ← mkCoeffE r
  -- 2. Ring operations
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    mkAddE (← reify a) (← reify b)
  | HMul.hMul _ _ _ _ a b =>
    mkMulE (← reify a) (← reify b)
  | HSub.hSub _ _ _ _ a b =>
    mkSubE (← reify a) (← reify b)
  | Neg.neg _ _ a =>
    mkNegE (← reify a)
  | HPow.hPow _ _ _ _ a b =>
    if let some k ← getNatLit? b then
      mkPowE (← reify a) k
    else
      mkVarE (← mkVar e)
  | _ =>
    -- 3. Everything else → variable
    mkVarE (← mkVar e)

/-- Result of reification. -/
structure Result where
  /-- The reified expression (Lean Expr of type AlgExpr C). -/
  algExpr : Expr
  /-- Variables collected (A-expressions, indexed by Var). -/
  vars : Array Expr

/--
Try to build a reification context from a detected Algebra R A instance.
Returns `none` if synthesis fails.
-/
def mkRContext? (R A : Expr) : MetaM (Option RContext) := do
  -- Extract universe levels: getLevel returns u+1 for Type u, we need u
  let uR' ← getLevel R
  let uA' ← getLevel A
  let uR := match uR' with | .succ u => u | u => u
  let uA := match uA' with | .succ u => u | u => u
  -- Synthesize instances manually with correct universe levels
  let csRType := mkApp (mkConst ``Lean.Grind.CommSemiring [uR]) R
  let csR ← try synthInstance csRType
    catch _ => return none
  let sAType := mkApp (mkConst ``Lean.Grind.Semiring [uA]) A
  let sA ← try synthInstance sAType
    catch _ => return none
  let algType := mkApp4 (mkConst ``Lean.Grind.Algebra [uR, uA]) R A csR sA
  let algInst ← try synthInstance algType
    catch _ => return none
  -- Build algebraMap R A (partially applied)
  let algebraMapFn := mkApp5 (mkConst ``Lean.Grind.algebraMap [uR, uA]) R A csR sA algInst
  return some { R, A, uR, uA, algebraMapFn }

/-- Run reification on a Lean expression given a context. -/
def run (ctx : RContext) (e : Expr) : MetaM Result := do
  let (algExpr, state) ← (reify e).run ctx |>.run {}
  return { algExpr, vars := state.vars }

end Macaulean.AlgPoly.Reify
