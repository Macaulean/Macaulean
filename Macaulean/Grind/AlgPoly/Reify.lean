/- 
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Expr
import Macaulean.Grind.Algebra.Instances
import Lean.Data.RArray
import Lean.Meta.Basic
import Lean.Meta.Eval
import Lean.Meta.SynthInstance
import Lean.Meta.WHNF

/-!
# Reification helpers for `AlgPoly`

This module houses the shared reflection layer used by `algebra_norm` and
certificate checkers built on top of `AlgPoly`.

The key design is the same one used by the current reflective tactic:

- coefficients are reified into `Lean.Grind.CommRing.Expr` and normalized to
  `Lean.Grind.CommRing.Poly`
- ambient algebra expressions are reified into `AlgExpr Poly`
- denotation is interpreted through `algebraMap`

This keeps the coefficient normalization story aligned with `grind`'s own
commutative-ring infrastructure.
-/

open Lean Meta
open Lean.Grind

namespace Macaulean.AlgPoly.Reify

theorem polyCoeffIsRingHom {R : Type} {A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (coeffCtx : Lean.Grind.CommRing.Context R) :
    Macaulean.AlgPoly.IsRingHom
      (fun p : Lean.Grind.CommRing.Poly =>
        algebraMap R A (Lean.Grind.CommRing.Poly.denote coeffCtx p)) := by
  refine {
    map_zero := ?_
    map_one := ?_
    map_add := ?_
    map_mul := ?_
    map_neg := ?_
  }
  · simpa [Lean.Grind.CommRing.Poly.denote, Ring.intCast_zero] using
      (Lean.Grind.Algebra.algebraMap_zero (R := R) (A := A))
  · simpa [Lean.Grind.CommRing.Poly.denote, Ring.intCast_one] using
      (Lean.Grind.Algebra.algebraMap_one (R := R) (A := A))
  · intro a b
    change algebraMap R A (Lean.Grind.CommRing.Poly.denote coeffCtx (Lean.Grind.CommRing.Poly.combine a b)) = _
    rw [Lean.Grind.CommRing.Poly.denote_combine, Lean.Grind.Algebra.algebraMap_add]
  · intro a b
    change algebraMap R A (Lean.Grind.CommRing.Poly.denote coeffCtx (Lean.Grind.CommRing.Poly.mul a b)) = _
    rw [Lean.Grind.CommRing.Poly.denote_mul, Lean.Grind.Algebra.algebraMap_mul]
  · intro a
    change algebraMap R A (Lean.Grind.CommRing.Poly.denote coeffCtx (Lean.Grind.CommRing.Poly.mulConst (-1) a)) = _
    rw [Lean.Grind.CommRing.Poly.denote_mulConst, Lean.Grind.Algebra.algebraMap_mul]
    rw [Ring.intCast_neg_one, Lean.Grind.Algebra.algebraMap_neg, Lean.Grind.Algebra.algebraMap_one]
    simpa [Lean.Grind.Algebra.algebraMap_neg, Lean.Grind.Algebra.algebraMap_one, Lean.Grind.Semiring.one_mul] using
      (Ring.neg_mul (1 : A) (algebraMap R A (Lean.Grind.CommRing.Poly.denote coeffCtx a)))

def polyType : Expr :=
  mkConst ``Lean.Grind.CommRing.Poly

def getTypeLevel (type : Expr) : MetaM Level := do
  let u' ← getLevel type
  pure <| match u' with
    | .succ u => u
    | u => u

private def mkNatZero (type : Expr) : MetaM Expr := do
  let u ← getTypeLevel type
  let semiringInstType := mkApp (mkConst ``Lean.Grind.Semiring [u]) type
  let semiringInst ← synthInstance semiringInstType
  let natCastInst := mkApp2 (mkConst ``Lean.Grind.Semiring.natCast [u]) type semiringInst
  pure <| mkApp3 (mkConst ``NatCast.natCast [u]) type natCastInst (mkNatLit 0)

def mkContextExpr (type : Expr) (vars : Array Expr) : MetaM Expr := do
  if h : 0 < vars.size then
    Lean.RArray.toExpr type id (Lean.RArray.ofFn (vars[·]) h)
  else
    Lean.RArray.toExpr type id (Lean.RArray.leaf (← mkNatZero type))

private def mkCoeffExprCtor (declName : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst declName) args

private def mkAlgExprCtor (declName : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst declName [.zero]) (#[polyType] ++ args)

def mkPolyValueExpr (p : Lean.Grind.CommRing.Poly) : Expr :=
  Lean.Meta.Grind.Arith.CommRing.ofPoly p

def mkMonValueExpr (m : Lean.Grind.CommRing.Mon) : Expr :=
  Lean.Meta.Grind.Arith.CommRing.ofMon m

def mkAlgPolyValueExpr : Macaulean.AlgPoly Lean.Grind.CommRing.Poly → Expr
  | .coeff k =>
      mkAppN (mkConst ``Macaulean.AlgPoly.coeff [.zero]) #[polyType, mkPolyValueExpr k]
  | .add k m p =>
      mkAppN (mkConst ``Macaulean.AlgPoly.add [.zero])
        #[polyType, mkPolyValueExpr k, mkMonValueExpr m, mkAlgPolyValueExpr p]

structure State where
  coeffVars : Array Expr := #[]
  coeffVarMap : Std.HashMap Expr Nat := {}
  ambientVars : Array Expr := #[]
  ambientVarMap : Std.HashMap Expr Nat := {}

abbrev ReifyM := StateT State MetaM

private def mkCoeffVar (e : Expr) : ReifyM Nat := do
  let s ← get
  match s.coeffVarMap[e]? with
  | some idx => pure idx
  | none =>
    let idx := s.coeffVars.size
    modify fun s => { s with
      coeffVars := s.coeffVars.push e
      coeffVarMap := s.coeffVarMap.insert e idx
    }
    pure idx

private def mkAmbientVar (e : Expr) : ReifyM Nat := do
  let s ← get
  match s.ambientVarMap[e]? with
  | some idx => pure idx
  | none =>
    let idx := s.ambientVars.size
    modify fun s => { s with
      ambientVars := s.ambientVars.push e
      ambientVarMap := s.ambientVarMap.insert e idx
    }
    pure idx

private def mkCoeffVarExpr (idx : Nat) : Expr :=
  mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.var #[mkRawNatLit idx]

private def mkCoeffLitNat (n : Nat) : Expr :=
  mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.num #[mkIntLit n]

private def mkCoeffLitInt (n : Int) : Expr :=
  mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.intCast #[mkIntLit n]

partial def reifyCoeffExpr (e : Expr) : ReifyM Expr := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    pure <| mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.add #[← reifyCoeffExpr a, ← reifyCoeffExpr b]
  | HMul.hMul _ _ _ _ a b =>
    pure <| mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.mul #[← reifyCoeffExpr a, ← reifyCoeffExpr b]
  | HSub.hSub _ _ _ _ a b =>
    pure <| mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.sub #[← reifyCoeffExpr a, ← reifyCoeffExpr b]
  | Neg.neg _ _ a =>
    pure <| mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.neg #[← reifyCoeffExpr a]
  | HPow.hPow _ _ _ _ a b =>
    match (← getNatValue? b) with
    | some k => pure <| mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.pow #[← reifyCoeffExpr a, mkRawNatLit k]
    | none => mkCoeffVarExpr <$> mkCoeffVar e
  | IntCast.intCast _ _ a =>
    match (← getIntValue? a) with
    | some k => pure <| mkCoeffLitInt k
    | none => mkCoeffVarExpr <$> mkCoeffVar e
  | NatCast.natCast _ _ a =>
    match (← getNatValue? a) with
    | some k => pure <| mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.natCast #[mkNatLit k]
    | none => mkCoeffVarExpr <$> mkCoeffVar e
  | OfNat.ofNat _ n _ =>
    match (← getNatValue? n) with
    | some k => pure <| mkCoeffLitNat k
    | none => mkCoeffVarExpr <$> mkCoeffVar e
  | _ =>
    mkCoeffVarExpr <$> mkCoeffVar e

def mkCoeffPolyExpr (e : Expr) : ReifyM Expr := do
  pure <| mkApp (mkConst ``Lean.Grind.CommRing.Expr.toPoly) (← reifyCoeffExpr e)

private def isAlgebraMapApp? (algebraMapFn e : Expr) : MetaM (Option Expr) := do
  if e.isApp then
    let fn := e.appFn!
    let arg := e.appArg!
    if ← isDefEq fn algebraMapFn then
      return some arg
  return none

private def mkAmbientCoeff (coeff : Expr) : Expr :=
  mkAlgExprCtor ``AlgExpr.coeff #[coeff]

private def mkAmbientVarExpr (idx : Nat) : Expr :=
  mkAlgExprCtor ``AlgExpr.var #[mkRawNatLit idx]

partial def reifyAmbientExpr (algebraMapFn : Expr) (e : Expr) : ReifyM Expr := do
  if let some coeffExpr ← liftM <| isAlgebraMapApp? algebraMapFn e then
    return mkAmbientCoeff (← mkCoeffPolyExpr coeffExpr)
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    pure <| mkAlgExprCtor ``AlgExpr.add #[← reifyAmbientExpr algebraMapFn a, ← reifyAmbientExpr algebraMapFn b]
  | HMul.hMul _ _ _ _ a b =>
    pure <| mkAlgExprCtor ``AlgExpr.mul #[← reifyAmbientExpr algebraMapFn a, ← reifyAmbientExpr algebraMapFn b]
  | HSub.hSub _ _ _ _ a b =>
    pure <| mkAlgExprCtor ``AlgExpr.sub #[← reifyAmbientExpr algebraMapFn a, ← reifyAmbientExpr algebraMapFn b]
  | Neg.neg _ _ a =>
    pure <| mkAlgExprCtor ``AlgExpr.neg #[← reifyAmbientExpr algebraMapFn a]
  | HPow.hPow _ _ _ _ a b =>
    match (← getNatValue? b) with
    | some k => pure <| mkAlgExprCtor ``AlgExpr.pow #[← reifyAmbientExpr algebraMapFn a, mkRawNatLit k]
    | none => mkAmbientVarExpr <$> mkAmbientVar e
  | IntCast.intCast _ _ a =>
    match (← getIntValue? a) with
    | some k => pure <| mkAmbientCoeff (mkApp (mkConst ``Lean.Grind.CommRing.Expr.toPoly) (mkCoeffLitInt k))
    | none => mkAmbientVarExpr <$> mkAmbientVar e
  | NatCast.natCast _ _ a =>
    match (← getNatValue? a) with
    | some k => pure <| mkAmbientCoeff (mkApp (mkConst ``Lean.Grind.CommRing.Expr.toPoly)
        (mkCoeffExprCtor ``Lean.Grind.CommRing.Expr.natCast #[mkNatLit k]))
    | none => mkAmbientVarExpr <$> mkAmbientVar e
  | OfNat.ofNat _ n _ =>
    match (← getNatValue? n) with
    | some k => pure <| mkAmbientCoeff (mkApp (mkConst ``Lean.Grind.CommRing.Expr.toPoly) (mkCoeffLitNat k))
    | none => mkAmbientVarExpr <$> mkAmbientVar e
  | _ =>
    mkAmbientVarExpr <$> mkAmbientVar e

structure CoeffResult where
  polyExpr : Expr
  vars : Array Expr

structure AmbientResult where
  algExpr : Expr
  coeffVars : Array Expr
  ambientVars : Array Expr

structure AmbientPairResult where
  lhsAlgExpr : Expr
  rhsAlgExpr : Expr
  coeffVars : Array Expr
  ambientVars : Array Expr

def runCoeff (e : Expr) : MetaM CoeffResult := do
  let (polyExpr, s) ← (mkCoeffPolyExpr e).run {}
  pure { polyExpr, vars := s.coeffVars }

unsafe def evalCoeffPoly (e : Expr) : MetaM (Lean.Grind.CommRing.Poly × Array Expr) := do
  let result ← runCoeff e
  let poly ← evalExpr Lean.Grind.CommRing.Poly polyType result.polyExpr
  pure (poly, result.vars)

def runAmbient (algebraMapFn : Expr) (e : Expr) : MetaM AmbientResult := do
  let (algExpr, s) ← (reifyAmbientExpr algebraMapFn e).run {}
  pure { algExpr, coeffVars := s.coeffVars, ambientVars := s.ambientVars }

def runAmbientPair (algebraMapFn lhs rhs : Expr) : MetaM AmbientPairResult := do
  let ((lhsAlgExpr, rhsAlgExpr), s) ← (do
      let lhsAlgExpr ← reifyAmbientExpr algebraMapFn lhs
      let rhsAlgExpr ← reifyAmbientExpr algebraMapFn rhs
      pure (lhsAlgExpr, rhsAlgExpr)
    ).run {}
  pure {
    lhsAlgExpr,
    rhsAlgExpr,
    coeffVars := s.coeffVars,
    ambientVars := s.ambientVars
  }

end Macaulean.AlgPoly.Reify
