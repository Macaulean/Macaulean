import Lean
import Macaulean.CAS
import Macaulean.Serialize
import Macaulean.IdealMembership

open Lean Grind Elab Tactic Meta

namespace Macaulean.Polyrith

theorem eq_of_sub_eq_zero [Lean.Grind.Ring R] {a b : R} (h : a - b = 0) : a = b :=
  Lean.Grind.AddCommGroup.sub_eq_zero_iff.mp h

structure HypInfo where
  fvarId : FVarId
  name : Name
  lhsExpr : Lean.Expr
  rhsExpr : Lean.Expr

private def parseEq? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr) :=
  match e.getAppFn with
  | .const ``Eq _ =>
    let args := e.getAppArgs
    if args.size == 3 then some (args[0]!, args[1]!, args[2]!) else none
  | _ => none

private def scanContextForEqHyps (type : Expr) : TacticM (Array HypInfo) := do
  let ctx ← getLCtx
  let mut hyps := #[]
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    match parseEq? declType with
    | some (hypType, lhs, rhs) =>
      if ← isDefEq hypType type then
        hyps := hyps.push {
          fvarId := decl.fvarId, name := decl.userName,
          lhsExpr := lhs, rhsExpr := rhs
        }
    | none => continue
  pure hyps

private def resolveNamedHyps (type : Expr) (idents : Array Syntax) : TacticM (Array HypInfo) := do
  let ctx ← getLCtx
  let mut hyps := #[]
  for ident in idents do
    let name := ident.getId
    let some decl := ctx.findFromUserName? name
      | throwError "unknown hypothesis '{name}'"
    let declType ← instantiateMVars decl.type
    match parseEq? declType with
    | some (hypType, lhs, rhs) =>
      unless ← isDefEq hypType type do
        throwError "hypothesis '{name}' is not an equality over {type}"
      hyps := hyps.push {
        fvarId := decl.fvarId, name, lhsExpr := lhs, rhsExpr := rhs
      }
    | none =>
      throwError "hypothesis '{name}' is not an equality"
  pure hyps

private def mkMul (a b : Expr) : MetaM Expr :=
  mkAppM ``HMul.hMul #[a, b]

private def mkAdd (a b : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[a, b]

private def mkSub (a b : Expr) : MetaM Expr :=
  mkAppM ``HSub.hSub #[a, b]

private def proveByTactic (goalType : Expr) (tac : Syntax) : TacticM Expr := do
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic tac
  finally
    setGoals savedGoals
  instantiateMVars mvar

private def buildLinearCombExpr (type : Lean.Expr) (vars : Array Lean.Expr)
    (quotientPolys : Array Lean.Grind.CommRing.Poly) (hyps : Array HypInfo) :
    TacticM Lean.Expr := do
  let mut acc? : Option Lean.Expr := none
  for (hyp, qPoly) in hyps.zip quotientPolys do
    let qi ← Macaulean.mkPolyExpr type vars qPoly
    let diffI ← mkSub hyp.lhsExpr hyp.rhsExpr
    let term ← mkMul qi diffI
    acc? ← match acc? with
      | none => pure (some term)
      | some acc => pure (some (← mkAdd acc term))
  match acc? with
  | some acc => pure acc
  | none => mkNumeral type 0

private def polyrithCore (hyps : Array HypInfo) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some (type, lhsExpr, rhsExpr) := parseEq? target
    | throwTacticEx `m2polyrith goal "Expected an equality goal `lhs = rhs`"

  if hyps.isEmpty then
    throwTacticEx `m2polyrith goal "No usable equality hypotheses found"

  -- Reify all expressions with shared variable state
  let action : Macaulean.PolyReifyM
      (Lean.Grind.CommRing.Expr × Lean.Grind.CommRing.Expr ×
       Array (Lean.Grind.CommRing.Expr × Lean.Grind.CommRing.Expr)) := do
    let lhsRE ← Macaulean.reifyRingExpr lhsExpr
    let rhsRE ← Macaulean.reifyRingExpr rhsExpr
    let hypREs ← hyps.mapM fun hyp => do
      let aRE ← Macaulean.reifyRingExpr hyp.lhsExpr
      let bRE ← Macaulean.reifyRingExpr hyp.rhsExpr
      pure (aRE, bRE)
    pure (lhsRE, rhsRE, hypREs)

  let ((lhsRE, rhsRE, hypREs), state) ← action.run { vars := #[] }
  let vars := state.vars

  -- Compute target and generator polynomials
  let targetPoly := lhsRE.toPoly.combine (rhsRE.toPoly.mulConst (-1))
  let genPolys := hypREs.map fun (aRE, bRE) =>
    aRE.toPoly.combine (bRE.toPoly.mulConst (-1))

  -- Serialize and call M2
  let targetMRDI : MRDI.Poly := { data := targetPoly.serialize }
  let idealData : MRDI.Ideal := {
    numVars := vars.size
    generators := genPolys.map (·.serialize)
  }

  let session ← Macaulean.CAS.globalMacaulay2Session
  let witness ←
    try
      Macaulean.CAS.quotientRemainderUsingBackend session targetMRDI idealData
    catch e =>
      throwError m!"m2polyrith: backend call failed: {e.toMessageData}"

  unless witness.idealMembershipJudgment?.isSome do
    throwTacticEx `m2polyrith goal
      "Macaulay2 could not express the goal as a consequence of the given hypotheses"

  -- Deserialize quotients
  let quotientPolys ← witness.quotients.toList.mapM fun q =>
    pure (Lean.Grind.CommRing.PolynomialData.deserialize q.data)
  let quotientPolys := quotientPolys.toArray

  -- Build the linear combination expression: e = Σ q_i * (a_i - b_i)
  let e ← buildLinearCombExpr type vars quotientPolys hyps

  -- Prove h_ring : lhs - rhs = e (pure polynomial identity)
  let subExpr ← mkSub lhsExpr rhsExpr
  let hRingType ← mkEq subExpr e
  let hRing ← proveByTactic hRingType (← `(tactic| grind))

  -- Prove h_zero : e = 0 (using hypotheses in context)
  let zeroExpr ← mkNumeral type 0
  let hZeroType ← mkEq e zeroExpr
  let hZero ← proveByTactic hZeroType (← `(tactic| grind))

  -- Chain: lhs - rhs = 0
  let hSubZero ← mkAppM ``Eq.trans #[hRing, hZero]

  -- Conclude: lhs = rhs
  let finalProof ← mkAppM ``Macaulean.Polyrith.eq_of_sub_eq_zero #[hSubZero]

  goal.assign finalProof
  setGoals ((← getGoals).erase goal)

syntax (name := m2polyrith) "m2polyrith" (" only " "[" ident,* "]")? : tactic

@[tactic m2polyrith] def evalM2Polyrith : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some (type, _, _) := parseEq? target
    | throwTacticEx `m2polyrith goal "Expected an equality goal `lhs = rhs`"
  let hyps ←
    if stx[1].isNone then
      scanContextForEqHyps type
    else
      -- stx[1] is the optional group: " only " "[" ident,* "]"
      let idents := stx[1][2].getSepArgs
      resolveNamedHyps type idents
  polyrithCore hyps

end Macaulean.Polyrith
