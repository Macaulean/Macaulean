import Lean
import Macaulean.CAS.Strategy
import Macaulean.CAS.Tactic
import MRDI.CAS

open Lean Grind Elab Tactic Meta
open MRDI.CAS

-- ============================================================================
-- Mathematical definitions (unchanged)
-- ============================================================================

abbrev IsUnit [CommSemiring R] (a : R) : Prop :=
  ∃ b : R, b*a = 1

structure Irreducible [CommSemiring R] (p : R) : Prop where
  not_isUnit : ¬IsUnit p
  isUnit_or_isUnit ⦃a b : R⦄ : p = a * b → IsUnit a ∨ IsUnit b

theorem factorizationImpliesReducible {a b : R} [CommSemiring R] : ¬ (IsUnit a ∨ IsUnit b) → ¬ Irreducible (a * b) := by
  intro p
  apply Not.intro
  intro irr
  let ⟨_ , unitImp ⟩ := irr
  have abUnit : _ := unitImp (by trivial : a*b = a*b)
  contradiction

def factorizationExpr (factorization : List (Nat × Nat)) : MetaM Expr := do
  match factorization with
      | [] => pure $ mkNatLit 1
      | (a,e) :: remainder => remainder.foldlM (fun x (a,e) =>  mkPowerExpr (mkNatLit a) (mkNatLit e) >>= mkProductExpr x) $ (← mkPowerExpr (mkNatLit a) (mkNatLit e))
  where
    mkProductExpr a b := mkAppM ``HMul.hMul #[a,b]
    mkPowerExpr a b := mkAppM ``HPow.hPow #[a,b]

-- ============================================================================
-- Shared: call CAS for factorization
-- ============================================================================

private def callFactorNat (ctx : Macaulean.CAS.CASContext) (n : Nat) : TacticM (List (Nat × Nat)) := do
  let problem : FactorizationProblem := { n }
  let response ← ctx.call (toMrdi problem)
  let result ← match fromMrdi? (α := FactorizationResult) response with
    | .ok r => pure r
    | .error e => throwError s!"Failed to decode factorization result: {e}"
  pure result.factors.toList

-- ============================================================================
-- Strategy: Factorization (m2factor)
-- ============================================================================

private def executeFactorNat (_ : Macaulean.CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  throwTacticEx `cas goal "factorNat strategy should be called via m2factor wrapper"

-- ============================================================================
-- Strategy: Reducibility (¬ Irreducible n)
-- ============================================================================

private def executeReducibility (ctx : Macaulean.CAS.CASContext) (goal : MVarId) :
    TacticM (List MVarId) := do
  let target ← goal.getType
  let (``Not, #[irrExpr]) := target.getAppFnArgs
    | throwTacticEx `cas goal "Expected a goal of the form ¬ Irreducible x"
  let (``Irreducible, #[_, _, irrTarget]) := irrExpr.getAppFnArgs
    | throwTacticEx `cas goal "Expected a goal of the form ¬ Irreducible x"
  let .lit (Literal.natVal x) ← whnf irrTarget
    | throwTacticEx `cas goal "Expected a goal of the form ¬ Irreducible x"
  let factorization ← callFactorNat ctx x
  match factorization with
  | [] | [(_, 0)] | [(_, 1)] =>
      throwTacticEx `cas goal m!"Cannot prove reducibility of {x}"
  | _ =>
      let factoredExpr ← factorizationExpr factorization
      let factorEqExpr ← mkAppM ``Eq #[mkNatLit x, factoredExpr]
      let factorizationMVarExpr ← mkFreshExprMVar $ .some factorEqExpr
      let factorizationMVarId := factorizationMVarExpr.mvarId!
      pushGoal factorizationMVarId
      _ ← runTactic factorizationMVarId (← `(tactic| decide))
      let rewriteResult ← goal.rewrite (← goal.getType) factorizationMVarExpr
      let newGoal ← goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
      setGoals [newGoal]
      setGoals (← newGoal.apply $ mkConst ``factorizationImpliesReducible [.zero])
      _ ← runTactic (← getMainGoal) (← `(tactic| grind))
      pure []

initialize do
  Macaulean.CAS.registerCASStrategy {
    name := `reducibility
    priority := 1000
    match? := fun goal => do
      let target ← goal.getType
      let (fn, args) := target.getAppFnArgs
      if fn == ``Not then
        if let #[irrExpr] := args then
          return irrExpr.isAppOf ``Irreducible
      pure false
    execute := executeReducibility
  }

-- ============================================================================
-- Legacy tactic wrappers
-- ============================================================================

syntax (name := m2factor) "m2factor" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic m2factor]
def macaulay2ProvideFactorization : Tactic := fun stx => do
  match stx with
  | `(tactic| m2factor $x_stx:term) =>
      let x_expr ← elabTermEnsuringType x_stx (.some $ Expr.const ``Nat [])
      let .lit (Literal.natVal x) ← Meta.whnf x_expr
        | throwTacticEx `m2factor (← getMainGoal) m!"Expected a Nat but got {x_expr}"
      let ctx ← Macaulean.CAS.mkCASContext
      try
        let factorization ← callFactorNat ctx x
        let factorizationExpr ← factorizationExpr factorization
        closeMainGoal `m2factor factorizationExpr
      finally
        ctx.cleanup
  | _ => throwUnsupportedSyntax

elab "m2reducible" : tactic => do
  evalTactic (← `(tactic| cas))
