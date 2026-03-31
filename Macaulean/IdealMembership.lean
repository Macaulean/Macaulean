import Lean
import Macaulean.CAS.Strategy
import Macaulean.CAS.Tactic
import Macaulean.CAS.Reify
import Macaulean.Serialize
import MRDI.CAS

open Lean Grind Elab Tactic Meta
open Lean.Grind.CommRing
open MRDI.CAS

namespace Macaulean

-- ============================================================================
-- Mathematical definitions (unchanged)
-- ============================================================================

def linearCombination [CommRing R] : List R → List R → R
  | q :: qs, g :: gs => q * g + linearCombination qs gs
  | _, _ => 0

def InIdeal [CommRing R] (element : R) (generators : List R) : Prop :=
  ∃ quotients : List R, linearCombination quotients generators = element

-- ============================================================================
-- Strategy: Ideal Membership via Polynomial Reduction
-- ============================================================================

private def executeIdealMembership (ctx : CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  let target ← goal.getType
  let (targetFn, targetArgs) := target.getAppFnArgs
  unless targetFn == ``Macaulean.InIdeal && targetArgs.size == 4 do
    throwTacticEx `cas goal "Expected a goal of the form `InIdeal p [g₁, ..., gₙ]`"
  let element := targetArgs[2]!
  let generatorsExpr := targetArgs[3]!
  let some generators ← getListLit? generatorsExpr
    | throwTacticEx `cas goal "Expected an explicit list of generators"
  -- Reify into MRDI polynomial data
  let (vars, elementPoly, generatorPolys) ← CAS.Reify.reifyPolys element generators
  -- Build MRDI ReductionProblem
  let ring : PolyRing := { coeff := .int, vars := (List.range vars.size).toArray.map (s!"x{·}") }
  let problem : ReductionProblem := {
    element := { ring, data := elementPoly.data }
    ideal := { ring, generators := generatorPolys.map (·.data) }
    order := .grevlex
  }
  let response ← ctx.call (toMrdi problem)
  let result ← match fromMrdi? (α := ReductionResult) response with
    | .ok r => pure r
    | .error e => throwTacticEx `cas goal s!"Failed to decode reduction result: {e}"
  -- Check remainder is zero
  let remainderPoly := PolynomialData.deserialize result.remainder
  unless remainderPoly == .num 0 do
    throwTacticEx `cas goal "CAS did not certify that the element is in the ideal"
  -- Build quotient expressions and introduce existential witness
  let type ← inferType element
  let quotientExprs ← result.quotients.toList.mapM fun quotient =>
    CAS.Reify.mkPolyExpr type vars (PolynomialData.deserialize quotient)
  let quotientListExpr ← mkListLit type quotientExprs
  let newGoal ← goal.existsIntro quotientListExpr
  -- Close the equality subgoal
  setGoals [newGoal]
  evalTactic (← `(tactic| simp [Macaulean.linearCombination]))
  let remainingGoals ← getGoals
  unless remainingGoals.isEmpty do
    evalTactic (← `(tactic| grind))
  pure (← getGoals)

initialize do
  CAS.registerCASStrategy {
    name := `idealMembership
    priority := 1000
    match? := fun goal => do
      let target ← goal.getType
      pure (target.isAppOf ``Macaulean.InIdeal)
    execute := executeIdealMembership
  }

-- ============================================================================
-- Legacy tactic wrapper
-- ============================================================================

syntax (name := m2ideal_member) "m2ideal_member" : tactic

@[tactic m2ideal_member] def evalM2IdealMember : Tactic := fun _ => do
  evalTactic (← `(tactic| cas))

end Macaulean
