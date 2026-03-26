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

## Strategy

1. Try reflective two-level normalization first. The ambient algebra layer uses
   `AlgPoly`, and coefficients are reified into Lean's normalized
   `Lean.Grind.CommRing.Poly`.
2. Keep the previous `grind`/`simp` pipeline as a fallback for unsupported
   syntax and goals the reflective path does not parse directly.
-/

open Lean Meta Elab Tactic

namespace Macaulean.AlgPoly.Tactic

open Lean.Grind

namespace Reflect
private structure Inputs where
  R : Expr
  A : Expr
  algebraMapFn : Expr
  algebraInst : Expr
  lhs : Expr
  rhs : Expr
  lhsReified : Expr
  rhsReified : Expr
  coeffVars : Array Expr
  ambientVars : Array Expr

private def findAlgebraMapFn? (e : Expr) : Option Expr :=
  match e.find? fun sub =>
      sub.isApp &&
      let fn := sub.appFn!
      match fn.getAppFn with
      | .const ``Lean.Grind.algebraMap _ => fn.getAppNumArgs == 5
      | _ => false with
  | some app => some app.appFn!
  | none => none

private def getEqSides? (target : Expr) : Option (Expr × Expr) :=
  match target.getAppFn with
  | .const ``Eq _ =>
    let args := target.getAppArgs
    if args.size == 3 then some (args[1]!, args[2]!) else none
  | _ => none

private def buildInputs (target : Expr) : TacticM Inputs := do
  let some (lhs, rhs) := getEqSides? target
    | throwError "reflective algebra_norm only handles equality goals"
  let some algebraMapFn := findAlgebraMapFn? target
    | throwError "no algebraMap occurrence found"
  let .const ``Lean.Grind.algebraMap _ := algebraMapFn.getAppFn
    | throwError "unexpected algebraMap head"
  let args := algebraMapFn.getAppArgs
  let R := args[0]!
  let A := args[1]!
  let algebraInst := args[4]!
  let reified ← Macaulean.AlgPoly.Reify.runAmbientPair algebraMapFn lhs rhs
  pure {
    R, A, algebraMapFn, algebraInst, lhs, rhs,
    lhsReified := reified.lhsAlgExpr,
    rhsReified := reified.rhsAlgExpr,
    coeffVars := reified.coeffVars,
    ambientVars := reified.ambientVars
  }

private def proveDefinallyEq (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic (← `(tactic| rfl))
  finally
    setGoals savedGoals
  instantiateMVars mvar

partial def proveNormalizedDenoteEq (A : Expr) (coeffPolyDenote : Expr) (ambientCtx : Expr)
    (lhs rhs : Macaulean.AlgPoly Lean.Grind.CommRing.Poly) : TacticM Expr := do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
  let ringAType := mkApp (mkConst ``Lean.Grind.Ring [uA]) A
  let ringAInst ← synthInstance ringAType
  let polyDenoteFn := mkConst ``Macaulean.AlgPoly.denote [.zero, uA]
  let lhsExpr := mkAppN polyDenoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      A,
      ringAInst,
      coeffPolyDenote,
      ambientCtx,
      Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr lhs
    ]
  let rhsExpr := mkAppN polyDenoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      A,
      ringAInst,
      coeffPolyDenote,
      ambientCtx,
      Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr rhs
    ]
  let goalType ← mkEq lhsExpr rhsExpr
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic (← `(tactic|
      simp [
        Macaulean.AlgPoly.denote,
        Lean.Grind.CommRing.Poly.denote,
        Lean.Grind.CommRing.Mon.denote,
        Lean.Grind.CommRing.Mon.denote_ofVar,
        Lean.Grind.CommRing.Power.denote_eq,
        Lean.Grind.CommRing.Var.denote,
        Lean.RArray.get,
        Nat.ble,
        Lean.Grind.Algebra.algebraMap_add,
        Lean.Grind.Algebra.algebraMap_sub,
        Lean.Grind.Algebra.algebraMap_mul,
        Lean.Grind.Algebra.algebraMap_neg,
        Lean.Grind.Algebra.algebraMap_zero,
        Lean.Grind.Algebra.algebraMap_one,
        Lean.Grind.Semiring.zero_mul,
        Lean.Grind.AddCommMonoid.zero_add
      ]))
    if !(← getGoals).isEmpty then
      evalTactic (← `(tactic| grind))
      evalTactic (← `(tactic| done))
  finally
    setGoals savedGoals
  instantiateMVars mvar

private unsafe def proveReifiedEq (inputs : Inputs) : TacticM Expr := withMainContext do
  let coeffCtx ← liftM <| Macaulean.AlgPoly.Reify.mkContextExpr inputs.R inputs.coeffVars
  let ambientCtx ← liftM <| Macaulean.AlgPoly.Reify.mkContextExpr inputs.A inputs.ambientVars
  let uR ← Macaulean.AlgPoly.Reify.getTypeLevel inputs.R
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel inputs.A
  let commRingRType := mkApp (mkConst ``Lean.Grind.CommRing [uR]) inputs.R
  let commRingAType := mkApp (mkConst ``Lean.Grind.CommRing [uA]) inputs.A
  let commRingRInst ← synthInstance commRingRType
  let commRingAInst ← synthInstance commRingAType
  let ringRType := mkApp (mkConst ``Lean.Grind.Ring [uR]) inputs.R
  let ringAType := mkApp (mkConst ``Lean.Grind.Ring [uA]) inputs.A
  let ringRInst ← synthInstance ringRType
  let ringAInst ← synthInstance ringAType
  let coeffPolyDenote := mkLambda `p .default Macaulean.AlgPoly.Reify.polyType <|
    mkApp inputs.algebraMapFn <|
      mkAppN (mkConst ``Lean.Grind.CommRing.Poly.denote [uR])
        #[inputs.R, ringRInst, coeffCtx, mkBVar 0]
  let hφ := mkAppN (mkConst ``Macaulean.AlgPoly.Reify.polyCoeffIsRingHom)
      #[inputs.R, inputs.A, commRingRInst, commRingAInst, inputs.algebraInst, coeffCtx]
  let coeffRingPolyInst ← synthInstance
    (mkApp (mkConst ``Macaulean.CoeffRing [.zero]) Macaulean.AlgPoly.Reify.polyType)
  let lhsPoly := mkAppN (mkConst ``Macaulean.AlgExpr.toAlgPoly [.zero])
    #[Macaulean.AlgPoly.Reify.polyType, coeffRingPolyInst, inputs.lhsReified]
  let rhsPoly := mkAppN (mkConst ``Macaulean.AlgExpr.toAlgPoly [.zero])
    #[Macaulean.AlgPoly.Reify.polyType, coeffRingPolyInst, inputs.rhsReified]
  let denoteFn := mkConst ``Macaulean.AlgExpr.denote [.zero, uA]
  let polyDenoteFn := mkConst ``Macaulean.AlgPoly.denote [.zero, uA]
  let denoteLhs := mkAppN denoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      inputs.A,
      commRingAInst,
      coeffPolyDenote,
      ambientCtx,
      inputs.lhsReified
    ]
  let denoteRhs := mkAppN denoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      inputs.A,
      commRingAInst,
      coeffPolyDenote,
      ambientCtx,
      inputs.rhsReified
    ]
  let proveBridge (lhs rhs : Expr) : TacticM Expr := do
    let goalType ← mkEq lhs rhs
    let mvar ← mkFreshExprMVar goalType
    let savedGoals ← getGoals
    setGoals [mvar.mvarId!]
    try
      evalTactic (← `(tactic|
        simp [
          Macaulean.AlgExpr.denote,
          Lean.Grind.CommRing.Expr.denote,
          Lean.Grind.CommRing.Expr.denote_toPoly,
          Lean.Grind.CommRing.denoteInt_eq,
          Lean.Grind.CommRing.Var.denote,
          Lean.RArray.get,
          Nat.ble,
          Lean.Grind.Algebra.algebraMap_add,
          Lean.Grind.Algebra.algebraMap_sub,
          Lean.Grind.Algebra.algebraMap_mul,
          Lean.Grind.Algebra.algebraMap_neg,
          Lean.Grind.Algebra.algebraMap_zero,
          Lean.Grind.Algebra.algebraMap_one
        ]))
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| grind))
        evalTactic (← `(tactic| done))
    finally
      setGoals savedGoals
    instantiateMVars mvar
  let hLhs ←
    try
      proveBridge denoteLhs inputs.lhs
    catch e =>
      throwError m!"lhs bridge failed: {e.toMessageData}"
  let hRhs ←
    try
      proveBridge denoteRhs inputs.rhs
    catch e =>
      throwError m!"rhs bridge failed: {e.toMessageData}"
  try
    let beqTerm ← mkAppM ``BEq.beq #[lhsPoly, rhsPoly]
    let beqEq ← mkEq beqTerm (mkConst ``true)
    let hBeqMVar ← mkFreshExprMVar beqEq
    let savedGoals ← getGoals
    setGoals [hBeqMVar.mvarId!]
    try
      evalTactic (← `(tactic| decide))
    finally
      setGoals savedGoals
    let hBeq ← instantiateMVars hBeqMVar
    let core :=
      mkAppN (mkConst ``Macaulean.AlgExpr.eq_of_toAlgPoly_eq [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          inputs.A,
          coeffRingPolyInst,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          inputs.lhsReified,
          inputs.rhsReified,
          hBeq
        ]
    let hLhsSymm ← mkEqSymm hLhs
    let hCoreRhs ← mkEqTrans core hRhs
    mkEqTrans hLhsSymm hCoreRhs
  catch _ =>
    let algPolyType := mkApp (mkConst ``Macaulean.AlgPoly [.zero]) Macaulean.AlgPoly.Reify.polyType
    let lhsNorm ← evalExpr (Macaulean.AlgPoly Lean.Grind.CommRing.Poly) algPolyType lhsPoly
    let rhsNorm ← evalExpr (Macaulean.AlgPoly Lean.Grind.CommRing.Poly) algPolyType rhsPoly
    let lhsNormExpr := Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr lhsNorm
    let rhsNormExpr := Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr rhsNorm
    let lhsNormDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        lhsNormExpr
      ]
    let rhsNormDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        rhsNormExpr
      ]
    let lhsPolyDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        lhsPoly
      ]
    let rhsPolyDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        rhsPoly
      ]
    let core ←
      try
        proveNormalizedDenoteEq inputs.A coeffPolyDenote ambientCtx lhsNorm rhsNorm
      catch e =>
        throwError m!"normalized denotation proof failed: {e.toMessageData}"
    let hNormLhs ←
      try
        proveDefinallyEq lhsNormDenote lhsPolyDenote
      catch e =>
        throwError m!"lhs normalization bridge failed: {e.toMessageData}"
    let hNormRhs ←
      try
        proveDefinallyEq rhsNormDenote rhsPolyDenote
      catch e =>
        throwError m!"rhs normalization bridge failed: {e.toMessageData}"
    let hToPolyLhs :=
      mkAppN (mkConst ``Macaulean.AlgExpr.denote_toAlgPoly [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          coeffRingPolyInst,
          inputs.A,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          inputs.lhsReified
        ]
    let hToPolyRhs :=
      mkAppN (mkConst ``Macaulean.AlgExpr.denote_toAlgPoly [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          coeffRingPolyInst,
          inputs.A,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          inputs.rhsReified
        ]
    let hNormLhsGoal ← mkEqTrans hNormLhs hToPolyLhs
    let hNormRhsGoal ← mkEqTrans hNormRhs hToPolyRhs
    let hNormLhsGoal ← mkEqTrans hNormLhsGoal hLhs
    let hNormRhsGoal ← mkEqTrans hNormRhsGoal hRhs
    let hNormLhsGoalSymm ← mkEqSymm hNormLhsGoal
    let hCoreRhs ← mkEqTrans core hNormRhsGoal
    mkEqTrans hNormLhsGoalSymm hCoreRhs

private unsafe def solveGoal : TacticM Unit := withMainContext do
  let mainGoal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let inputs ← buildInputs target
  let proof ← instantiateMVars (← proveReifiedEq inputs)
  if proof.hasMVar then
    throwError m!"reflective proof has metavariables: {proof}"
  mainGoal.assign proof
  setGoals ((← getGoals).erase mainGoal)

end Reflect

private unsafe def reflectOnly : TacticM Unit := do
  let s ← get
  let mut directErr : MessageData := m!""
  try
    Reflect.solveGoal
    return
  catch e =>
    directErr := e.toMessageData
    set s
  try
    evalTactic (← `(tactic| simp only [Lean.Grind.Algebra.algebraMap_smul_def]))
    if (← getGoals).isEmpty then
      return
  catch e =>
    throwError m!"algebra_norm_reflect could not solve the goal\n\
      direct attempt: {directErr}\n\
      after smul preprocessing: {e.toMessageData}"
  try
    Reflect.solveGoal
    return
  catch e =>
    set s
    let _ := e
    throwError m!"algebra_norm_reflect could not solve the goal\n\
      direct attempt: {directErr}\n\
      after smul preprocessing: reflective normalization failed"

elab "algebra_norm_reflect" : tactic => do
  unsafe do
    reflectOnly

elab "algebra_norm" : tactic => do
  unsafe do
    let s ← get
    try
      reflectOnly
      return
    catch _ =>
      set s
    -- Fallback 1: try grind directly (handles hypotheses, simple identities)
    try
      evalTactic (← `(tactic| grind))
      return
    catch _ => pure ()
    -- Fallback 2: contract algebraMap products/sums + grind
    try
      evalTactic (← `(tactic|
        (simp (config := { maxSteps := 200000 }) only [
          ← Lean.Grind.Algebra.algebraMap_mul, ← Lean.Grind.Algebra.algebraMap_add,
          ← Lean.Grind.Algebra.algebraMap_sub, ← Lean.Grind.Semiring.mul_assoc,
          ← Lean.Grind.Semiring.right_distrib,
          Lean.Grind.Algebra.algebraMap_smul_def];
         grind)))
      return
    catch _ => pure ()
    -- Fallback 3: expand algebraMap via simp, then grind
    evalTactic (← `(tactic|
      (simp (config := { maxSteps := 200000 }) only [
        Lean.Grind.Algebra.algebraMap_add, Lean.Grind.Algebra.algebraMap_mul,
        Lean.Grind.Algebra.algebraMap_sub, Lean.Grind.Algebra.algebraMap_neg,
        Lean.Grind.Algebra.algebraMap_zero, Lean.Grind.Algebra.algebraMap_one,
        Lean.Grind.Algebra.algebraMap_smul_def];
       grind)))

end Macaulean.AlgPoly.Tactic
