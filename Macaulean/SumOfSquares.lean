import Lean
import Macaulean.CAS
import Macaulean.Serialize
import Init.Data.Rat.Lemmas
import Init.Grind.Ordered.Rat

open Lean Grind Elab Tactic Meta

namespace Macaulean.SumOfSquares

theorem weightedSq_nonnegRat (w : Nat) (q : Rat) : 0 ≤ (w : Rat) * q^2 := by
  apply Rat.mul_nonneg
  exact Rat.natCast_nonneg
  exact OrderedRing.sq_nonneg

theorem nonneg_of_natScale_nonnegRat {x : Rat} {k : Nat}
    (hk : 0 < k) (h : 0 ≤ (k : Rat) * x) : 0 ≤ x := by
  have hz : (k : Rat) * 0 ≤ (k : Rat) * x := by
    simpa [Semiring.zero_mul] using h
  exact Rat.le_of_mul_le_mul_left hz (Rat.natCast_pos.mpr hk)

structure SosWitness (p : Rat) where
  scale : Nat
  scale_pos : 0 < scale
  witness : Rat
  witness_nonneg : 0 ≤ witness
  equality : (scale : Rat) * p = witness

theorem SosWitness.proves_nonneg {p : Rat} (w : SosWitness p) : 0 ≤ p := by
  have hScaled : 0 ≤ (w.scale : Rat) * p := by
    simpa [w.equality] using w.witness_nonneg
  exact nonneg_of_natScale_nonnegRat (k := w.scale) w.scale_pos hScaled

private inductive ReflectedVar where
  | indeterminate (idx : Nat)
  | ratConst (value : Rat)

private structure RatTerm where
  coeff : Rat
  mon : MRDI.Monomial

private structure ClearedPolynomial where
  scale : Nat
  vars : Array Expr
  polyData : MRDI.PolynomialData

private structure PolyReifyState where
  vars : Array Expr := #[]

private abbrev PolyReifyM := StateRefT PolyReifyState MetaM

private def addVar (e : Expr) : PolyReifyM Nat := do
  let e ← instantiateMVars e.consumeMData
  let state ← get
  match state.vars.findIdx? fun other => other == e with
  | some idx => pure idx
  | none =>
      modify fun state => { state with vars := state.vars.push e }
      pure state.vars.size

private partial def evalRatExpr? (e : Expr) : MetaM (Option Rat) := do
  let e ← instantiateMVars e.consumeMData
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
      let oa ← evalRatExpr? a
      let ob ← evalRatExpr? b
      return oa.bind fun qa => ob.map fun qb => qa + qb
  | HMul.hMul _ _ _ _ a b =>
      let oa ← evalRatExpr? a
      let ob ← evalRatExpr? b
      return oa.bind fun qa => ob.map fun qb => qa * qb
  | HSub.hSub _ _ _ _ a b =>
      let oa ← evalRatExpr? a
      let ob ← evalRatExpr? b
      return oa.bind fun qa => ob.map fun qb => qa - qb
  | HDiv.hDiv _ _ _ _ a b =>
      let oa ← evalRatExpr? a
      let ob ← evalRatExpr? b
      return oa.bind fun qa => ob.map fun qb => qa / qb
  | HSMul.hSMul _ _ _ _ a b =>
      let oa ← evalRatExpr? a
      let ob ← evalRatExpr? b
      return oa.bind fun qa => ob.map fun qb => qa * qb
  | Neg.neg _ _ a =>
      return (← evalRatExpr? a).map fun qa => -qa
  | Inv.inv _ _ a =>
      return (← evalRatExpr? a).map fun qa => qa⁻¹
  | HPow.hPow _ _ _ _ a b =>
      match (← getNatValue? b), (← evalRatExpr? a) with
      | some k, some qa => return some (qa ^ k)
      | _, _ => return none
  | IntCast.intCast _ _ a =>
      return (← getIntValue? a).map fun z => (z : Rat)
  | NatCast.natCast _ _ a =>
      return (← getNatValue? a).map fun n => (n : Rat)
  | OfNat.ofNat _ n _ =>
      return (← getNatValue? n).map fun k => (k : Rat)
  | _ =>
      if e.isAppOfArity ``Rat.ofInt 1 then
        return (← getIntValue? e.appArg!).map fun z => (z : Rat)
      else
        return none

private partial def reifyRatPolyExpr (e : Expr) : PolyReifyM Lean.Grind.CommRing.Expr := do
  let e ← instantiateMVars e.consumeMData
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
      return .add (← reifyRatPolyExpr a) (← reifyRatPolyExpr b)
  | HSub.hSub _ _ _ _ a b =>
      return .sub (← reifyRatPolyExpr a) (← reifyRatPolyExpr b)
  | HMul.hMul _ _ _ _ a b =>
      return .mul (← reifyRatPolyExpr a) (← reifyRatPolyExpr b)
  | HSMul.hSMul _ _ _ _ a b =>
      if let some qa ← evalRatExpr? a then
        return .mul (.var (← addVar (toExpr qa))) (← reifyRatPolyExpr b)
      else
        return .var (← addVar e)
  | HDiv.hDiv _ _ _ _ a b =>
      if let some qb ← evalRatExpr? b then
        if qb == 0 then
          return .var (← addVar e)
        else
          return .mul (← reifyRatPolyExpr a) (.var (← addVar (toExpr qb⁻¹)))
      else
        return .var (← addVar e)
  | HPow.hPow _ _ _ _ a b =>
      let some k ← getNatValue? b
        | return .var (← addVar e)
      return .pow (← reifyRatPolyExpr a) k
  | Neg.neg _ _ a =>
      return .neg (← reifyRatPolyExpr a)
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
      if let some q ← evalRatExpr? e then
        return .var (← addVar (toExpr q))
      else
        return .var (← addVar e)

private def classifyReflectedVars (vars : Array Expr) : TacticM (Array ReflectedVar × Array Expr) := do
  let mut classes : Array ReflectedVar := #[]
  let mut indeterminates : Array Expr := #[]
  for v in vars do
    if v.isFVar then
      classes := classes.push (.indeterminate indeterminates.size)
      indeterminates := indeterminates.push v
    else
      match (← evalRatExpr? v) with
      | some q =>
          classes := classes.push (.ratConst q)
      | none =>
          throwError m!"m2sos encountered an unsupported subterm:{indentExpr v}"
  pure (classes, indeterminates)

private def substituteReflectedTerm (classes : Array ReflectedVar) (term : MRDI.Term) :
    TacticM RatTerm := do
  let mut coeff : Rat := term.coeff
  let mut mon : MRDI.Monomial := #[]
  for pw in term.mon.toList do
    let some cls := classes[pw.x]?
      | throwError m!"reflected coefficient variable x{toString pw.x} is missing"
    match cls with
    | .indeterminate idx =>
        mon := mon.push { x := idx, k := pw.k }
    | .ratConst q =>
        coeff := coeff * q^pw.k
  pure { coeff, mon }

private def clearRatTerms (terms : Array RatTerm) : TacticM (Nat × MRDI.PolynomialData) := do
  let scale := terms.foldl (init := 1) fun acc term => Nat.lcm acc term.coeff.den
  let mut polyData : MRDI.PolynomialData := #[]
  for term in terms do
    let scaledCoeff : Rat := (scale : Rat) * term.coeff
    if scaledCoeff.den != 1 then
      throwError "internal error: failed to clear SOS coefficient denominators"
    let coeff := scaledCoeff.num
    if coeff != 0 then
      polyData := polyData.push { coeff, mon := term.mon }
  if polyData.isEmpty then
    pure (scale, #[{ coeff := 0, mon := #[] }])
  else
    pure (scale, polyData)

private def clearReflectedPoly (poly : Lean.Grind.CommRing.Poly) (vars : Array Expr) :
    TacticM ClearedPolynomial := do
  let (classes, indeterminates) ← classifyReflectedVars vars
  let serialized := poly.serialize
  let terms ← serialized.mapM (substituteReflectedTerm classes)
  let (scale, polyData) ← clearRatTerms terms
  pure { scale, vars := indeterminates, polyData }

private def proveByTactic (goalType : Expr) (tac : Syntax) : TacticM Expr := do
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic tac
  finally
    setGoals savedGoals
  instantiateMVars mvar

private def mkMul (a b : Expr) : MetaM Expr :=
  mkAppM ``HMul.hMul #[a, b]

private def mkAdd (a b : Expr) : MetaM Expr :=
  mkAppM ``HAdd.hAdd #[a, b]

private def mkPow (a : Expr) (k : Nat) : MetaM Expr :=
  mkAppM ``HPow.hPow #[a, mkNatLit k]

private def mkZeroRat : Expr := toExpr (0 : Rat)

private def mkOneRat : Expr := toExpr (1 : Rat)

private def mkCoeffExpr (q : Rat) : Expr := toExpr q

private partial def monomialToExpr (vars : Array Expr) (mon : MRDI.Monomial) : MetaM Expr := do
  let mut acc? : Option Expr := none
  for pw in mon.toList do
    let some x := vars[pw.x]? | throwError m!"certificate references missing variable x{toString pw.x}"
    let powExpr ←
      if pw.k == 1 then pure x else mkPow x pw.k
    acc? ← match acc? with
      | none => pure (some powExpr)
      | some acc => pure (some (← mkMul acc powExpr))
  match acc? with
  | some acc => pure acc
  | none => pure mkOneRat

private def termToExpr (vars : Array Expr) (term : MRDI.Term) : MetaM Expr := do
  if term.coeff == 0 then
    pure mkZeroRat
  else if term.mon.isEmpty then
    pure <| mkCoeffExpr (term.coeff : Rat)
  else
    let monExpr ← monomialToExpr vars term.mon
    if term.coeff == 1 then
      pure monExpr
    else if term.coeff == -1 then
      mkAppM ``Neg.neg #[monExpr]
    else
      mkMul (mkCoeffExpr (term.coeff : Rat)) monExpr

private def polyDataToExpr (vars : Array Expr) (poly : MRDI.PolynomialData) : MetaM Expr := do
  let mut acc? : Option Expr := none
  for term in poly.toList do
    if term.coeff != 0 then
      let termExpr ← termToExpr vars term
      acc? ← match acc? with
        | none => pure (some termExpr)
        | some acc => pure (some (← mkAdd acc termExpr))
  match acc? with
  | some acc => pure acc
  | none => pure mkZeroRat

private def summandToExpr (vars : Array Expr) (summand : CAS.SumOfSquaresSummand) : MetaM Expr := do
  let qExpr ← polyDataToExpr vars summand.poly.data
  let sqExpr ← mkPow qExpr 2
  if summand.weight == 0 then
    pure mkZeroRat
  else if summand.weight == 1 then
    pure sqExpr
  else
    mkMul (mkCoeffExpr (summand.weight : Rat)) sqExpr

private partial def buildSosExprAndProof (vars : Array Expr)
    (summands : Array CAS.SumOfSquaresSummand) (start : Nat := 0) : TacticM (Expr × Expr) := do
  if h : start < summands.size then
    let summand := summands[start]
    let termExpr ← summandToExpr vars summand
    let qExpr ← polyDataToExpr vars summand.poly.data
    let termProof ←
      if summand.weight == 1 then
        proveByTactic (← mkAppM ``LE.le #[mkZeroRat, ← mkPow qExpr 2]) (← `(tactic| exact OrderedRing.sq_nonneg))
      else
        mkAppM ``Macaulean.SumOfSquares.weightedSq_nonnegRat #[mkNatLit summand.weight, qExpr]
    if hTail : start + 1 < summands.size then
      let (tailExpr, tailProof) ← buildSosExprAndProof vars summands (start + 1)
      let sumExpr ← mkAdd termExpr tailExpr
      let sumProof ← mkAppM ``Rat.add_nonneg #[termProof, tailProof]
      pure (sumExpr, sumProof)
    else
      pure (termExpr, termProof)
  else
    pure (mkZeroRat, ← proveByTactic (← mkAppM ``LE.le #[mkZeroRat, mkZeroRat]) (← `(tactic| exact Eq.le rfl)))

private def getGoalPolyExpr? (target : Expr) : MetaM (Option Expr) := do
  match_expr target with
  | LE.le _ _ lhs rhs =>
      match (← evalRatExpr? lhs) with
      | some lhsVal => pure <| if lhsVal == 0 then some rhs else none
      | none => pure none
  | _ => pure none

private def getWitnessPolyExpr? (target : Expr) : MetaM (Option Expr) := do
  let target ← whnf target
  if target.getAppFn.constName? == some ``Macaulean.SumOfSquares.SosWitness then
    pure target.getAppArgs.back?
  else
    pure none

private def reifyPolynomial (polyExpr : Expr) :
    TacticM (Lean.Grind.CommRing.Poly × Array Expr) := do
  let action : PolyReifyM Lean.Grind.CommRing.Expr := reifyRatPolyExpr polyExpr
  let (expr, state) ← action.run { vars := #[] }
  pure (expr.toPoly, state.vars)

private unsafe def buildWitnessExpr (origPolyExpr : Expr) : TacticM Expr := withMainContext do
  let (poly, reflectedVars) ← reifyPolynomial origPolyExpr
  let cleared ← clearReflectedPoly poly reflectedVars
  let session ← Macaulean.CAS.globalMacaulay2Session
  let cert ← Macaulean.CAS.sumOfSquaresUsingBackend session { data := cleared.polyData }
  unless cert.nonnegativityJudgment?.isSome do
    throwError "internal error: SOS backend did not derive nonnegativity"
  let totalScale := cleared.scale * cert.scale
  if totalScale == 0 then
    throwError "internal error: SOS witness returned zero total scale"
  let natPosType ← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit totalScale]
  let natPosProof ← proveByTactic natPosType (← `(tactic| decide))
  let (sosExpr, sosProof) ← buildSosExprAndProof cleared.vars cert.summands
  let hEqType ← mkEq (← mkMul (toExpr (totalScale : Rat)) origPolyExpr) sosExpr
  let hEqProof ← proveByTactic hEqType (← `(tactic| grind))
  mkAppM ``Macaulean.SumOfSquares.SosWitness.mk
    #[mkNatLit totalScale, natPosProof, sosExpr, sosProof, hEqProof]

elab "m2sos_witness" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some polyExpr ← getWitnessPolyExpr? target
    | throwTacticEx `m2sos_witness goal
        "expected a goal of the form `Macaulean.SumOfSquares.SosWitness p`"
  let witnessExpr ← unsafe buildWitnessExpr polyExpr
  goal.assign witnessExpr
  setGoals ((← getGoals).erase goal)

syntax (name := m2sosWitnessTerm) "m2sos_witness% " term:max : term

macro_rules
  | `(m2sos_witness% $p) =>
      `(show Macaulean.SumOfSquares.SosWitness $p from by
          m2sos_witness)

elab "m2sos" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some polyExpr ← getGoalPolyExpr? target
    | throwTacticEx `m2sos goal
        "expected a goal of the form `0 ≤ p` over `Rat`"
  let witnessExpr ← unsafe buildWitnessExpr polyExpr
  let finalProof ← mkAppM ``Macaulean.SumOfSquares.SosWitness.proves_nonneg #[witnessExpr]
  goal.assign finalProof
  setGoals ((← getGoals).erase goal)

end Macaulean.SumOfSquares
