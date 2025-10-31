import Lean
import Macaulean.Macaulay2

open Lean Grind Elab Tactic

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
      let mkProductExpr a b := mkApp2 (Expr.const ``Nat.mul []) a b
      let mkPowerExpr a b := mkApp2 (Expr.const ``Nat.pow []) a b
      let factorizationExpr := factorization.foldl (fun x (a,e) =>  mkProductExpr x $ mkPowerExpr (mkNatLit a) (mkNatLit e)) $ mkNatLit 1
      closeMainGoal `m2factor factorizationExpr
  | _ => throwUnsupportedSyntax

  -- the returned Expr should be an expression of type ¬ Irreducible x
def macaulay2ProveReducible (x : Nat) : TacticM (Option Expr) := do
  let (m2Process,m2Server) <- startM2Server
  let factorization <- m2Server.factorNat x
  match factorization with
    | [] | [(a,1)] => pure .none
    | (a,e)::otherFactors =>
      let b := otherFactors.foldl (fun x (a',e') => x*(a'^e')) a^(e-1)
      let aExpr := mkNatLit a
      let bExpr := mkNatLit b
      let prodExpr := mkApp2 (Expr.const ``Nat.mul []) aExpr bExpr
      let factorExpr := mkApp2 (Expr.const ``Eq [.succ .zero]) prodExpr $ mkNatLit x
      --TODO: add goals to prove that a and b are not units, and use trivial to try to prove them then reduce Irreducible x to proving
      sorry

def twelve : Nat := 12
def factor12 : Nat := by m2factor twelve
#print factor12

def factor10 : Nat := by m2factor 10
#print factor10
