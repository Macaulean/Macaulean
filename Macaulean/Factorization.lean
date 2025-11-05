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

theorem natOnlyUnit {x : Nat} : IsUnit x ↔ x = 1 := by
  apply Iff.intro
  intro a
  cases a
  expose_names
  exact Nat.eq_one_of_mul_eq_one_left h
  intro
  exists 1
  simp
  trivial

theorem factorizationImpliesReducible {a b : Nat} : ¬ (IsUnit a ∨ IsUnit b) → ¬ Irreducible (a * b) := by
  intro p
  apply Not.intro
  intro irr
  let ⟨_ , unitImp ⟩ := irr
  have abUnit : _ := unitImp (by trivial : a*b = a*b)
  contradiction

def factorizationExpr (factorization : List (Nat × Nat)) : Expr :=
  match factorization with
      | [] => mkNatLit 1
      | (a,e) :: remainder => remainder.foldl (fun x (a,e) =>  mkProductExpr x $ mkPowerExpr (mkNatLit a) (mkNatLit e)) $ mkPowerExpr (mkNatLit a) (mkNatLit e)
  where
    mkProductExpr a b := mkApp2 (Expr.const ``Nat.mul []) a b
    mkPowerExpr a b := mkApp2 (Expr.const ``Nat.pow []) a b

--this syntax command is based on the one for intro, correct if wrong
syntax (name := m2factor) "m2factor" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic m2factor]
def macaualy2ProvideFactorization : Tactic := fun stx => do
  match stx with
  | `(tactic| m2factor $x_stx:term) =>
      let x_expr <- elabTermEnsuringType x_stx (.some $ Expr.const ``Nat [])
      let x_expr' <- Meta.whnf x_expr
      let x <- match x_expr' with
              | .lit (Literal.natVal x) => pure x
              | _ => throwError ("Expect a Nat " ++ repr x_expr)
      let (m2Process,m2Server) <- startM2Server
      let factorization <- m2Server.factorNat x
      let factorizationExpr := factorizationExpr factorization
      closeMainGoal `m2factor factorizationExpr
  | _ => throwUnsupportedSyntax

  -- the returned Expr should be an expression of type ¬ Irreducible x
def macaulay2ProveReducible (x : Nat) : TacticM Unit := do
  let (m2Process,m2Server) <- startM2Server
  let factorizationMVarExpr <- mkFreshExprMVar (.some $ Expr.const `Prop [])
  let factorizationMVarId := factorizationMVarExpr.mvarId!
  let factorization <- m2Server.factorNat x
  match factorization with
    | [] | [(a,0)] | [(a,1)] => throwError "Cannot prove reducibility"
    | _ =>
        --sorry the goal for now
        let goal <- getMainGoal
        admitGoal goal

  --closeMainGoal `macaulay $ by sorry

elab "m2reducible" : tactic => do
  IO.println "TEST"
  let target <- getMainTarget
  match target with
  | .app (.const ``Not _) (.app (.app (.app (.const ``Irreducible _) _) _) x_expr) =>
      let x_expr' <- whnf x_expr
      let x <- match x_expr' with
              | .lit (Literal.natVal x) => pure x
              | _ => throwError "Expected a goal of the form ¬ Irreducible x"
      macaulay2ProveReducible x
  | _ => throwError ("Expected a goal of the form ¬ Irreducible x" ++ repr target)


def twelve : Nat := 12
def factor12 : Nat := by m2factor twelve
#print factor12

def factor10 : Nat := by m2factor 10
#print factor10

theorem twelve_reducible : ¬ Irreducible 12 :=
  by m2reducible
