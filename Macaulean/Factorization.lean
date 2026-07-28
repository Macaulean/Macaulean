import Lean
import Macaulean.Macaulay2

open Lean Grind Elab Tactic Meta

--based on mathlib

--instead of what mathlib does which is setting up the class of all units and asking if the element belongs to it
--for simplicity we just check if the element has an inverse
abbrev IsUnit [CommSemiring R] (a : R) : Prop :=
  ∃ b : R, b*a = 1

--this is copied directly from mathlib
structure Irreducible [CommSemiring R] (p : R) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isUnit : ¬IsUnit p
  /-- If an irreducible element factors, then one factor is a unit. -/
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

--this syntax command is based on the one for intro, correct if wrong
syntax (name := m2factor) "m2factor" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic m2factor]
def macaualy2ProvideFactorization : Tactic := fun stx => do
  match stx with
  | `(tactic| m2factor $x_stx:term) =>
      let x_expr ← elabTermEnsuringType x_stx (.some $ Expr.const ``Nat [])
      let .lit (Literal.natVal x) ← Meta.whnf x_expr | throwTacticEx `m2factor (← getMainGoal) m!"Expected a Nat but got {x_expr}"
      let m2Server ← globalM2Server
      let factorization ← m2Server.factorNat x
      let factorizationExpr ← factorizationExpr factorization
      closeMainGoal `m2factor factorizationExpr
  | _ => throwUnsupportedSyntax

-- This will try to close a goal of the form ¬ Irreducible x
def macaulay2ProveReducible (x : Nat) : TacticM Unit := do
  let m2Server <- globalM2Server
  let factorization <- m2Server.factorNat x
  match factorization with
    | [] | [(_,0)] | [(_,1)] => throwTacticEx `m2reducible (← getMainGoal) m!"Cannot prove reducibility of {x}"
    | _ =>
        let factoredExpr ← factorizationExpr factorization
        let factorEqExpr ← mkAppM ``Eq #[mkNatLit x, factoredExpr]
        let factorizationMVarExpr ← mkFreshExprMVar $ .some factorEqExpr
        let factorizationMVarId := factorizationMVarExpr.mvarId!
        pushGoal factorizationMVarId
        --use decide to prove that the factorization is a factorization
        _ ← runTactic factorizationMVarId (← `(tactic|decide))
        --rewrite the goal with the expression
        let goal ← getMainGoal
        let rewriteResult ← goal.rewrite (← getMainTarget) factorizationMVarExpr -- (symm := true)
        let newGoal ← goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
        setGoals [newGoal]
        --use the factorization implies reducible theorem
        setGoals (← newGoal.apply $ mkConst ``factorizationImpliesReducible [.zero])
        --get grind to prove that things are not units
        _ ← runTactic (← getMainGoal) (← `(tactic|grind))
        pure ()

elab "m2reducible" : tactic => do
  let goal ← getMainGoal
  let target ← getMainTarget
  let mvar ← mkFreshExprMVar (.some <| Expr.const ``Nat [])
  let irrExpr ← mkAppM ``Not #[← mkAppM ``Irreducible #[mvar]]
  if ← isDefEq target irrExpr
  then
    let x' ← instantiateMVars mvar
    let .lit (.natVal x) ← whnf x'
      | throwTacticEx `m2reducible goal s!"Expected a goal of the form ¬ Irreducible x"
    macaulay2ProveReducible x
  else throwTacticEx `m2reducible goal "Expected a goal of the form ¬ Irreducible x"

