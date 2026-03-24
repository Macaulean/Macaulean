/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.Algebra.Instances
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Simp

/-!
# Algebra solver extension for `grind`

A solver extension that bridges the coefficient ring `R` and the algebra `A`,
making scalar multiplication and algebraMap visible to grind's Gröbner basis solver.

## Key mechanism

Grind's ring solver (`CommRing` module) only handles `HSMul Nat A` and `HSMul Int A`.
For a general `Algebra R A`, `r • x` is opaque to the ring solver.

This extension intercepts `HSMul R A` and pushes `r • x = algebraMap R A r * x`,
converting scalar multiplication into ring multiplication that the Gröbner basis can normalize.
-/

open Lean Meta Grind

namespace Lean.Meta.Grind.Algebra

/-- State for the algebra solver extension. -/
structure ExtState where
  /-- Set of smul terms we've already rewritten. -/
  processedSmuls : PHashSet ExprPtr := {}
  deriving Inhabited

end Lean.Meta.Grind.Algebra

/-- The algebra solver extension registration. -/
initialize algebraExt : SolverExtension Lean.Meta.Grind.Algebra.ExtState ←
  registerSolverExtension (return {})

namespace Lean.Meta.Grind.Algebra

/-- Check if a type is Nat or Int (already handled by the ring solver). -/
private def isNatOrInt (e : Expr) : Bool :=
  e.isConstOf ``Nat || e.isConstOf ``Int

/--
Process a scalar multiplication `HSMul.hSMul R A _ _ r x`.
If `R` is not `Nat`/`Int` and `Algebra R A` exists, push `r • x = algebraMap R A r * x`.
-/
private def processSmul (e : Expr) : GoalM Unit := do
  let_expr HSMul.hSMul R A _ _ r x := e | return ()
  if isNatOrInt R then return ()
  -- Check if already processed
  let state ← algebraExt.getState
  if state.processedSmuls.contains ⟨e⟩ then return ()
  -- Try to synthesize Algebra R A (and its prerequisites)
  let uR ← getLevel R
  let uA ← getLevel A
  let commSemiringR ← try synthInstance (mkApp (mkConst ``Lean.Grind.CommSemiring [uR]) R)
    catch _ => return ()
  let semiringA ← try synthInstance (mkApp (mkConst ``Lean.Grind.Semiring [uA]) A)
    catch _ => return ()
  let algInstType := mkApp4 (mkConst ``Lean.Grind.Algebra [uR, uA]) R A commSemiringR semiringA
  let algInst ← try synthInstance algInstType
    catch _ => return ()
  -- Mark as processed
  algebraExt.modifyState fun s => { s with processedSmuls := s.processedSmuls.insert ⟨e⟩ }
  -- Construct proof: Algebra.smul_def r x : r • x = Algebra.toFun r * x
  -- We need the proof in terms matching what the congruence closure expects
  let proof := mkApp7 (mkConst ``Lean.Grind.Algebra.algebraMap_smul_def
    [← getLevel R, ← getLevel A]) R A commSemiringR semiringA algInst r x
  -- Construct RHS: algebraMap R A r * x
  -- algebraMap R A = Lean.Grind.algebraMap R A = Algebra.toFun
  let algebraMapFn := mkApp5 (mkConst ``Lean.Grind.algebraMap
    [← getLevel R, ← getLevel A]) R A commSemiringR semiringA algInst
  let aMapR := mkApp algebraMapFn r
  let mulFn ← mkAppM ``HMul.hMul #[aMapR, x]
  pushEq e mulFn proof

/-- Internalize handler: called when grind internalizes a new term. -/
def internalize (e : Expr) (_parent? : Option Expr) : GoalM Unit := do
  processSmul e

/-- Equality handler: called when two marked terms become equal. -/
def processNewEq (_lhs _rhs : Expr) : GoalM Unit := do
  -- Congruence closure already handles: if r₁ = r₂ then algebraMap r₁ = algebraMap r₂.
  return ()

end Lean.Meta.Grind.Algebra

initialize
  algebraExt.setMethods
    (internalize := Lean.Meta.Grind.Algebra.internalize)
    (newEq := Lean.Meta.Grind.Algebra.processNewEq)
