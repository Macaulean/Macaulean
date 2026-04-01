import Lean
import Macaulean.IdealMembership
import Macaulean.CAS.Reify
import MRDI.CAS

open Lean Grind Elab Tactic Meta
open Lean.Grind.CommRing
open MRDI.CAS

namespace Macaulean

/-! # Gröbner Basis Tactics

Provides `gb_compute` for computing Gröbner bases and proving ideal membership
via Gröbner basis reduction. Backend-agnostic — works with any registered CAS
backend that supports `groebner_basis_problem` and `reduction_problem`.
-/

-- ============================================================================
-- Tactic: gb_reduce — prove f = 0 mod ideal via CAS reduction
-- ============================================================================

/-- `gb_reduce` proves a goal of the form `InIdeal f [g₁, ..., gₙ]` by
first computing a Gröbner basis, then reducing. This is more powerful than
direct reduction because the Gröbner basis ensures a canonical remainder. -/
private def executeGBReduce (ctx : CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  let target ← goal.getType
  let (targetFn, targetArgs) := target.getAppFnArgs
  unless targetFn == ``Macaulean.InIdeal && targetArgs.size == 4 do
    throwTacticEx `cas goal "Expected a goal of the form `InIdeal p [g₁, ..., gₙ]`"
  let element := targetArgs[2]!
  let generatorsExpr := targetArgs[3]!
  let some generators ← getListLit? generatorsExpr
    | throwTacticEx `cas goal "Expected an explicit list of generators"
  let (vars, elementPoly, generatorPolys) ← CAS.Reify.reifyPolys element generators
  let ring : PolyRing := { coeff := .int, vars := (List.range vars.size).toArray.map (s!"x{·}") }
  -- Step 1: Compute Gröbner basis of the ideal
  let gbProblem : GroebnerBasisProblem := {
    ring
    generators := generatorPolys.map (·.data)
    order := .grevlex
  }
  let gbResponse ← ctx.call (toMrdi gbProblem)
  let gbResult ← match fromMrdi? (α := GroebnerBasisResult) gbResponse with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode GB result: {e}"
  -- Step 2: Reduce element modulo the Gröbner basis
  let reductionProblem : ReductionProblem := {
    element := { ring, data := elementPoly.data }
    ideal := { ring, generators := gbResult.generators }
    order := .grevlex
  }
  let redResponse ← ctx.call (toMrdi reductionProblem)
  let redResult ← match fromMrdi? (α := ReductionResult) redResponse with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode reduction result: {e}"
  -- Check remainder is zero
  let remainderPoly := PolynomialData.deserialize redResult.remainder
  unless remainderPoly == .num 0 do
    throwTacticEx `cas goal "GB reduction: element is not in the ideal (nonzero remainder)"
  -- Now we need coefficients expressing element in terms of ORIGINAL generators,
  -- not the GB. Do a direct reduction against original generators.
  let directProblem : ReductionProblem := {
    element := { ring, data := elementPoly.data }
    ideal := { ring, generators := generatorPolys.map (·.data) }
    order := .grevlex
  }
  let directResponse ← ctx.call (toMrdi directProblem)
  let directResult ← match fromMrdi? (α := ReductionResult) directResponse with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode direct reduction: {e}"
  let directRemainder := PolynomialData.deserialize directResult.remainder
  unless directRemainder == .num 0 do
    throwTacticEx `cas goal "Direct reduction failed — element not expressible via original generators"
  -- Build proof from direct quotients
  let type ← inferType element
  let quotientExprs ← directResult.quotients.toList.mapM fun quotient =>
    CAS.Reify.mkPolyExpr type vars (PolynomialData.deserialize quotient)
  let quotientListExpr ← mkListLit type quotientExprs
  let newGoal ← goal.existsIntro quotientListExpr
  setGoals [newGoal]
  evalTactic (← `(tactic| simp [Macaulean.linearCombination]))
  let remainingGoals ← getGoals
  unless remainingGoals.isEmpty do
    evalTactic (← `(tactic| grind))
  pure (← getGoals)

-- Register with lower priority than the direct idealMembership strategy
-- so it only fires if direct reduction fails
initialize do
  CAS.registerCASStrategy {
    name := `gbReduce
    priority := 2000  -- higher number = tried after idealMembership (1000)
    match? := fun goal => do
      let target ← goal.getType
      pure (target.isAppOf ``Macaulean.InIdeal)
    execute := executeGBReduce
  }

-- ============================================================================
-- Radical Membership
-- ============================================================================

def InRadical [CommRing R] (f : R) (generators : List R) : Prop :=
  ∃ n : Nat, InIdeal (f ^ n) generators

private def executeRadicalMembership (ctx : CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  let target ← goal.getType
  let (targetFn, targetArgs) := target.getAppFnArgs
  unless targetFn == ``Macaulean.InRadical && targetArgs.size == 4 do
    throwTacticEx `cas goal "Expected a goal of the form `InRadical f [g₁, ..., gₙ]`"
  let element := targetArgs[2]!
  let generatorsExpr := targetArgs[3]!
  let some generators ← getListLit? generatorsExpr
    | throwTacticEx `cas goal "Expected an explicit list of generators"
  let (vars, elementPoly, generatorPolys) ← CAS.Reify.reifyPolys element generators
  let ring : PolyRing := { coeff := .int, vars := (List.range vars.size).toArray.map (s!"x{·}") }
  -- Call CAS for radical membership
  let problem : RadicalMembershipProblem := {
    element := { ring, data := elementPoly.data }
    ideal := { ring, generators := generatorPolys.map (·.data) }
  }
  let response ← ctx.call (toMrdi problem)
  let result ← match fromMrdi? (α := RadicalMembershipResult) response with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode radical membership result: {e}"
  -- Introduce the power n as existential witness
  let nExpr := mkNatLit result.power
  let goalAfterN ← goal.existsIntro nExpr
  -- Now goal is: InIdeal (f ^ n) [g₁, ..., gₖ]
  -- Introduce quotients as existential witness
  let type ← inferType element
  let quotientExprs ← result.quotients.toList.mapM fun quotient =>
    CAS.Reify.mkPolyExpr type vars (PolynomialData.deserialize quotient)
  let quotientListExpr ← mkListLit type quotientExprs
  let goalAfterQ ← goalAfterN.existsIntro quotientListExpr
  -- Close the equality subgoal
  setGoals [goalAfterQ]
  evalTactic (← `(tactic| simp [Macaulean.linearCombination, Macaulean.InIdeal, Macaulean.InRadical]))
  let remainingGoals ← getGoals
  unless remainingGoals.isEmpty do
    evalTactic (← `(tactic| grind))
  pure (← getGoals)

initialize do
  CAS.registerCASStrategy {
    name := `radicalMembership
    priority := 1000
    match? := fun goal => do
      let target ← goal.getType
      pure (target.isAppOf ``Macaulean.InRadical)
    execute := executeRadicalMembership
  }

-- ============================================================================
-- Polynomial Factorization Strategy
-- ============================================================================

/-- Match goals of the form `f = g₁ * g₂ * ... * gₖ` or more generally
any equality between ring expressions where the LHS could be factored. -/
private def executePolyFactorization (ctx : CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  let target ← goal.getType
  let some (_, lhs, _) := target.eq?
    | throwTacticEx `cas goal "Expected an equality goal"
  let type ← inferType lhs
  -- Reify the LHS
  let action : CAS.Reify.PolyReifyM Lean.Grind.CommRing.Expr := CAS.Reify.reifyRingExpr lhs
  let (lhsExpr, state) ← action.run { vars := #[] }
  let lhsPoly : MRDI.Poly := { data := lhsExpr.toPoly.serialize }
  let ring : PolyRing := { coeff := .int, vars := (List.range state.vars.size).toArray.map (s!"x{·}") }
  -- Ask CAS to factor it
  let problem : PolyFactorizationProblem := { ring, polynomial := lhsPoly.data }
  let response ← ctx.call (toMrdi problem)
  let result ← match fromMrdi? (α := PolyFactorizationResult) response with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode factorization result: {e}"
  if result.factors.isEmpty then
    throwTacticEx `cas goal "CAS returned empty factorization"
  -- Build the product expression from factors
  let factorExprs ← result.factors.toList.mapM fun factorData =>
    CAS.Reify.mkPolyExpr type state.vars (PolynomialData.deserialize factorData)
  let productExpr ← factorExprs.tail.foldlM (fun acc e => mkMul acc e) factorExprs.head!
  -- Construct proof: lhs = product via ring
  let eqGoal ← mkFreshExprMVar (← mkEq lhs productExpr)
  let eqGoalId := eqGoal.mvarId!
  -- Try to close lhs = product with ring
  setGoals [eqGoalId]
  try
    evalTactic (← `(tactic| grind))
  catch _ =>
    throwTacticEx `cas goal "CAS factorization did not produce a valid factoring (ring failed)"
  -- Now rewrite the original goal using this equality
  let rewriteResult ← goal.rewrite target eqGoal
  let newGoal ← goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
  setGoals [newGoal]
  -- The goal should now be product = rhs, try ring
  try
    evalTactic (← `(tactic| grind))
    pure (← getGoals)
  catch _ =>
    pure (← getGoals)

-- Register poly factorization strategy — matches equality goals involving ring expressions
-- Lower priority than ideal membership / radical membership since it's more speculative
initialize do
  CAS.registerCASStrategy {
    name := `polyFactorization
    priority := 3000
    match? := fun goal => do
      let target ← goal.getType
      pure (target.isAppOf ``Eq)
    execute := executePolyFactorization
  }

-- ============================================================================
-- Polynomial Divisibility
-- ============================================================================

/-- `PolyDivides a b` means `b = a * c` for some `c`.
The CAS factors `b`, checks if `a` is among the factors, and provides
the cofactor. The user doesn't need to know the cofactor. -/
def PolyDivides [CommRing R] (a b : R) : Prop :=
  ∃ c : R, b = a * c

private def executePolyDivides (ctx : CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  let target ← goal.getType
  let (targetFn, targetArgs) := target.getAppFnArgs
  unless targetFn == ``Macaulean.PolyDivides && targetArgs.size == 4 do
    throwTacticEx `cas goal "Expected a goal of the form `PolyDivides a b`"
  let divisor := targetArgs[2]!
  let dividend := targetArgs[3]!
  let type ← inferType divisor
  -- Reify both
  let reifyAction : CAS.Reify.PolyReifyM (CommRing.Expr × CommRing.Expr) := do
    let dsorExpr ← CAS.Reify.reifyRingExpr divisor
    let ddendExpr ← CAS.Reify.reifyRingExpr dividend
    pure (dsorExpr, ddendExpr)
  let ((divisorExpr, dividendExpr), reifyState) ← reifyAction.run { vars := #[] }
  let dividendPoly : MRDI.Poly := { data := dividendExpr.toPoly.serialize }
  let ring : PolyRing := { coeff := .int, vars := (List.range reifyState.vars.size).toArray.map (s!"x{·}") }
  -- Ask CAS to factor the dividend
  let problem : PolyFactorizationProblem := { ring, polynomial := dividendPoly.data }
  let response ← ctx.call (toMrdi problem)
  let result ← match fromMrdi? (α := PolyFactorizationResult) response with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode factorization: {e}"
  if result.factors.isEmpty then
    throwTacticEx `cas goal "CAS returned empty factorization"
  -- Deserialize all factors
  let factorPolys := result.factors.map PolynomialData.deserialize
  let divisorPoly := divisorExpr.toPoly
  -- Find which factor matches the divisor (or a scalar multiple)
  let mut cofactorIndices : Array Nat := #[]
  let mut divisorFound := false
  for i in [:factorPolys.size] do
    if factorPolys[i]! == divisorPoly then
      if !divisorFound then
        divisorFound := true
      else
        cofactorIndices := cofactorIndices.push i
    else
      cofactorIndices := cofactorIndices.push i
  unless divisorFound do
    -- Try negated divisor: if -a divides b, then a divides b too (absorb sign into cofactor)
    throwTacticEx `cas goal "Divisor not found among factors of dividend"
  -- Build cofactor expression: product of remaining factors
  if cofactorIndices.isEmpty then
    -- dividend = divisor * 1
    let oneExpr ← mkNumeral type 1
    let newGoal ← goal.existsIntro oneExpr
    setGoals [newGoal]
    evalTactic (← `(tactic| simp [Macaulean.PolyDivides]))
    let remaining ← getGoals
    unless remaining.isEmpty do
      evalTactic (← `(tactic| grind))
    pure (← getGoals)
  else
    let cofactorExprs ← cofactorIndices.toList.mapM fun i =>
      CAS.Reify.mkPolyExpr type reifyState.vars factorPolys[i]!
    let cofactorExpr ← cofactorExprs.tail.foldlM (fun acc e => mkMul acc e) cofactorExprs.head!
    let newGoal ← goal.existsIntro cofactorExpr
    setGoals [newGoal]
    -- Goal: b = a * cofactor — close with grind
    evalTactic (← `(tactic| grind))
    pure (← getGoals)

initialize do
  CAS.registerCASStrategy {
    name := `polyDivides
    priority := 1000
    match? := fun goal => do
      let target ← goal.getType
      pure (target.isAppOf ``Macaulean.PolyDivides)
    execute := executePolyDivides
  }

-- ============================================================================
-- Tactic syntax
-- ============================================================================

syntax (name := gb_reduce_tactic) "gb_reduce" : tactic

@[tactic gb_reduce_tactic] def evalGBReduce : Tactic := fun _ => do
  evalTactic (← `(tactic| cas))

end Macaulean
