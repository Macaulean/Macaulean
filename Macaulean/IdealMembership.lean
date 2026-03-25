import Lean
import Macaulean.CAS
import Macaulean.Serialize

open Lean Grind Elab Tactic Meta
open Lean.Grind.CommRing

namespace Macaulean

def linearCombination [CommRing R] : List R → List R → R
  | q :: qs, g :: gs => q * g + linearCombination qs gs
  | _, _ => 0

def InIdeal [CommRing R] (element : R) (generators : List R) : Prop :=
  ∃ quotients : List R, linearCombination quotients generators = element

private structure PolyReifyState where
  vars : Array Lean.Expr := #[]

private abbrev PolyReifyM := StateRefT PolyReifyState MetaM

private def addVar (e : Lean.Expr) : PolyReifyM Nat := do
  let e ← instantiateMVars e.consumeMData
  let state ← get
  match state.vars.findIdx? fun other => other == e with
  | some idx => pure idx
  | none =>
      modify fun state => { state with vars := state.vars.push e }
      pure state.vars.size

private partial def reifyRingExpr (e : Lean.Expr) : PolyReifyM Lean.Grind.CommRing.Expr := do
  let e ← instantiateMVars e.consumeMData
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
      return .add (← reifyRingExpr a) (← reifyRingExpr b)
  | HSub.hSub _ _ _ _ a b =>
      return .sub (← reifyRingExpr a) (← reifyRingExpr b)
  | HMul.hMul _ _ _ _ a b =>
      return .mul (← reifyRingExpr a) (← reifyRingExpr b)
  | HPow.hPow _ _ _ _ a b =>
      let some k ← getNatValue? b
        | return .var (← addVar e)
      return .pow (← reifyRingExpr a) k
  | Neg.neg _ _ a =>
      return .neg (← reifyRingExpr a)
  | IntCast.intCast _ _ a =>
      let some k ← getIntValue? a
        | return .var (← addVar e)
      return .intCast k
  | NatCast.natCast _ _ a =>
      let some k ← getNatValue? a
        | return .var (← addVar e)
      return .natCast k
  | OfNat.ofNat _ n _ =>
      let some k ← getNatValue? n
        | return .var (← addVar e)
      return .num k
  | _ =>
      return .var (← addVar e)

private def reifyPolys (element : Lean.Expr) (generators : Array Lean.Expr) :
    TacticM (Array Lean.Expr × MRDI.Poly × Array MRDI.Poly) := do
  let action : PolyReifyM (Lean.Grind.CommRing.Expr × Array Lean.Grind.CommRing.Expr) := do
    let elementExpr ← reifyRingExpr element
    let generatorExprs ← generators.mapM reifyRingExpr
    pure (elementExpr, generatorExprs)
  let ((elementExpr, generatorExprs), state) ← action.run { vars := #[] }
  let elementPoly : MRDI.Poly := { data := elementExpr.toPoly.serialize }
  let generatorPolys := generatorExprs.map fun generatorExpr =>
    ({ data := generatorExpr.toPoly.serialize } : MRDI.Poly)
  pure (state.vars, elementPoly, generatorPolys)

private def mkCoeffExpr (type : Lean.Expr) (k : Int) : MetaM Lean.Expr := do
  if k < 0 then
    mkAppM ``Neg.neg #[← mkNumeral type k.natAbs]
  else
    mkNumeral type k.natAbs

private def mkPowerExpr (base : Lean.Expr) (k : Nat) : MetaM Lean.Expr := do
  if k == 0 then
    mkNumeral (← inferType base) 1
  else if k == 1 then
    pure base
  else
    mkAppM ``HPow.hPow #[base, mkNatLit k]

private partial def mkMonomialExpr (type : Lean.Expr) (vars : Array Lean.Expr) (m : Mon) :
    MetaM Lean.Expr := do
  match m with
  | .unit =>
      mkNumeral type 1
  | .mult power rest =>
      let factor ← mkPowerExpr vars[power.x]! power.k
      match rest with
      | .unit =>
          pure factor
      | _ =>
          mkMul factor (← mkMonomialExpr type vars rest)

private def mkTermExpr (type : Lean.Expr) (vars : Array Lean.Expr) (k : Int) (m : Mon) :
    MetaM Lean.Expr := do
  match m with
  | .unit =>
      mkCoeffExpr type k
  | _ =>
      if k == 1 then
        mkMonomialExpr type vars m
      else if k == -1 then
        mkAppM ``Neg.neg #[← mkMonomialExpr type vars m]
      else
        mkMul (← mkCoeffExpr type k) (← mkMonomialExpr type vars m)

private partial def mkPolyExpr (type : Lean.Expr) (vars : Array Lean.Expr) (p : Poly) :
    MetaM Lean.Expr := do
  match p with
  | .num k =>
      mkCoeffExpr type k
  | .add k m p =>
      let termExpr ← mkTermExpr type vars k m
      match p with
      | .num 0 =>
          pure termExpr
      | _ =>
          mkAdd termExpr (← mkPolyExpr type vars p)

syntax (name := m2ideal_member) "m2ideal_member" : tactic

@[tactic m2ideal_member] def evalM2IdealMember : Tactic := fun _ => do
  let goal ← getMainGoal
  let target ← getMainTarget
  let (targetFn, targetArgs) := target.getAppFnArgs
  unless targetFn == ``Macaulean.InIdeal && targetArgs.size == 4 do
    throwTacticEx `m2ideal_member goal "Expected a goal of the form `InIdeal p [g₁, ..., gₙ]`"
  let element := targetArgs[2]!
  let generatorsExpr := targetArgs[3]!
  let some generators ← getListLit? generatorsExpr
    | throwTacticEx `m2ideal_member goal "Expected an explicit list of generators"
  let (vars, elementPoly, generatorPolys) ← reifyPolys element generators
  let idealData : MRDI.Ideal := {
    numVars := vars.size
    generators := generatorPolys.map (·.data)
  }
  let session ← Macaulean.CAS.globalMacaulay2Session
  let witness ← Macaulean.CAS.quotientRemainderUsingBackend session elementPoly idealData
  unless witness.idealMembershipJudgment?.isSome do
    throwTacticEx `m2ideal_member goal "Macaulay2 did not certify that the element is in the ideal"
  let type ← inferType element
  let quotientExprs ← witness.quotients.toList.mapM fun quotient =>
    mkPolyExpr type vars (Lean.Grind.CommRing.PolynomialData.deserialize quotient.data)
  let quotientListExpr ← mkListLit type quotientExprs
  let newGoal ← goal.existsIntro quotientListExpr
  replaceMainGoal [newGoal]
  evalTactic (← `(tactic| simp [Macaulean.linearCombination]))
  evalTactic (← `(tactic| grind))

end Macaulean
