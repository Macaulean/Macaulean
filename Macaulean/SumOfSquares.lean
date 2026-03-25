import Macaulean.Macaulay2
import Macaulean.Serialize
import Macaulean.Grind.AlgPoly.Reify
import Macaulean.Grind.AlgPoly.Tactic
import Macaulean.Grind.Algebra.Instances
import Lean.Elab.Tactic.Basic
import Lean.Meta.Eval
import Lean.Meta.Tactic.Simp
import Init.Data.Rat.Lemmas
import Init.Grind.FieldNormNum
import Init.Grind.Ordered.Field
import Init.Grind.Ordered.Rat

open Lean Meta Elab Tactic
open Lean.Grind

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

theorem algebraMap_rat_natCast {A : Type} [Lean.Grind.Field A] [Lean.Grind.Algebra Rat A] (n : Nat) :
    Lean.Grind.algebraMap Rat A (n : Rat) = Lean.Grind.Field.NormNum.ofRat (n : Rat) := by
  letI : NatCast A := Lean.Grind.Semiring.natCast (α := A)
  induction n with
  | zero =>
    rw [← Lean.Grind.Field.NormNum.natCast_eq (α := A) 0]
    simpa [Lean.Grind.Semiring.natCast_zero] using
      (Lean.Grind.Algebra.algebraMap_zero (R := Rat) (A := A))
  | succ n ih =>
    rw [← Lean.Grind.Field.NormNum.natCast_eq (α := A) (Nat.succ n)]
    have hsuccRat : ((Nat.succ n : Nat) : Rat) = (n : Rat) + 1 := by
      rw [Nat.succ_eq_add_one]
      simpa [Lean.Grind.Semiring.natCast_one] using (Lean.Grind.Semiring.natCast_add (α := Rat) n 1)
    rw [hsuccRat, Lean.Grind.Algebra.algebraMap_add, ih, Lean.Grind.Algebra.algebraMap_one]
    rw [← Lean.Grind.Field.NormNum.natCast_eq (α := A) n]
    simpa [Nat.succ_eq_add_one, Lean.Grind.Semiring.natCast_one] using
      (Lean.Grind.Semiring.natCast_add (α := A) n 1).symm

theorem weightedSq_nonneg {A : Type} [Lean.Grind.Field A]
    [LE A] [LT A] [Std.LawfulOrderLT A] [Std.IsLinearOrder A] [OrderedRing A]
    [Lean.Grind.Algebra Rat A]
    (w : Nat) (q : A) : 0 ≤ Lean.Grind.algebraMap Rat A (w : Rat) * q^2 := by
  apply OrderedRing.mul_nonneg
  · rw [algebraMap_rat_natCast (A := A) w]
    simpa [Lean.Grind.Field.NormNum.natCast_eq (α := A) w] using
      (OrderedRing.natCast_nonneg (R := A) (a := w))
  exact OrderedRing.sq_nonneg

theorem nonneg_of_natScale_nonneg {A : Type} [Lean.Grind.Field A]
    [LE A] [LT A] [Std.LawfulOrderLT A] [Std.IsLinearOrder A] [OrderedRing A]
    [Lean.Grind.Algebra Rat A]
    {x : A} {k : Nat}
    (hk : 0 < k) (h : 0 ≤ Lean.Grind.algebraMap Rat A (k : Rat) * x) : 0 ≤ x := by
  let c : A := Lean.Grind.algebraMap Rat A (k : Rat)
  have hc : 0 < c := by
    rw [show c = Lean.Grind.algebraMap Rat A (k : Rat) by rfl]
    rw [algebraMap_rat_natCast (A := A) k]
    simpa [Lean.Grind.Field.NormNum.natCast_eq (α := A) k] using
      (OrderedRing.pos_natCast_of_pos (R := A) k hk)
  have hz : c * (0 : A) ≤ c * x := by
    simpa [c, Semiring.mul_zero] using h
  exact (Lean.Grind.Field.IsOrdered.mul_le_mul_iff_of_pos_left (a := (0 : A)) (b := x) hc).mp hz

theorem add_nonneg {A : Type} [LE A] [Std.IsPreorder A] [AddCommMonoid A] [Lean.Grind.OrderedAdd A]
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  simpa [Lean.Grind.AddCommMonoid.zero_add] using Lean.Grind.OrderedAdd.add_le_add ha hb

theorem zero_nonneg {A : Type} [LE A] [Std.IsPreorder A] [AddCommMonoid A] : 0 ≤ (0 : A) :=
  by
    apply Std.IsPreorder.le_refl

structure SosWitness (A : Type) [Lean.Grind.Field A]
    [LE A] [LT A] [Std.LawfulOrderLT A] [Std.IsLinearOrder A] [OrderedRing A]
    [Lean.Grind.Algebra Rat A] (p : A) where
  scale : Nat
  scale_pos : 0 < scale
  witness : A
  witness_nonneg : 0 ≤ witness
  equality : Lean.Grind.algebraMap Rat A (scale : Rat) * p = witness

theorem SosWitness.proves_nonneg {A : Type} [Lean.Grind.Field A]
    [LE A] [LT A] [Std.LawfulOrderLT A] [Std.IsLinearOrder A] [OrderedRing A]
    [Lean.Grind.Algebra Rat A] {p : A} (w : SosWitness A p) : 0 ≤ p := by
  have hScaled : 0 ≤ Lean.Grind.algebraMap Rat A (w.scale : Rat) * p := by
    simpa [w.equality] using w.witness_nonneg
  exact nonneg_of_natScale_nonneg (A := A) (k := w.scale) w.scale_pos hScaled

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

private partial def evalRatExpr? (e : Expr) : MetaM (Option Rat) := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    match (← evalRatExpr? a), (← evalRatExpr? b) with
    | some qa, some qb => return some (qa + qb)
    | _, _ => return none
  | HMul.hMul _ _ _ _ a b =>
    match (← evalRatExpr? a), (← evalRatExpr? b) with
    | some qa, some qb => return some (qa * qb)
    | _, _ => return none
  | HSub.hSub _ _ _ _ a b =>
    match (← evalRatExpr? a), (← evalRatExpr? b) with
    | some qa, some qb => return some (qa - qb)
    | _, _ => return none
  | HDiv.hDiv _ _ _ _ a b =>
    match (← evalRatExpr? a), (← evalRatExpr? b) with
    | some qa, some qb => return some (qa / qb)
    | _, _ => return none
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
    if e.isAppOfArity ``Lean.Grind.Field.NormNum.ofRat 3 then
      getRatValue? e.getAppArgs[2]!
    else if e.isAppOfArity ``Lean.Grind.algebraMap 6 && e.getAppArgs[0]!.isConstOf ``Rat then
      evalRatExpr? e.getAppArgs[5]!
    else
      return none

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

private def getSmulSimpContext : MetaM Simp.Context := do
  let mut s : SimpTheorems := {}
  s ← s.addConst ``Lean.Grind.Algebra.algebraMap_smul_def
  Simp.mkContext
    (simpTheorems := #[s])
    (congrTheorems := (← getSimpCongrTheorems))

private def preprocessSosExpr (e : Expr) : MetaM (Expr × Expr) := do
  let ctx ← getSmulSimpContext
  let (r, _) ← Meta.simp e ctx
  let proof ←
    match r.proof? with
    | some h => pure h
    | none => mkEqRefl e
  pure (← instantiateMVars r.expr, ← instantiateMVars proof)

private def proveByTactic (goalType : Expr) (tac : Syntax) : TacticM Expr := do
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic tac
  finally
    setGoals savedGoals
  instantiateMVars mvar

private def mkMul (a b : Expr) : TacticM Expr :=
  mkAppM ``HMul.hMul #[a, b]

private def mkAdd (a b : Expr) : TacticM Expr :=
  mkAppM ``HAdd.hAdd #[a, b]

private def mkPow (a : Expr) (k : Nat) : TacticM Expr :=
  mkAppM ``HPow.hPow #[a, mkNatLit k]

private def mkOfRatExpr (A : Expr) (q : Rat) : TacticM Expr := do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
  let fieldAType := mkApp (mkConst ``Lean.Grind.Field [uA]) A
  let fieldAInst ← synthInstance fieldAType
  pure <| mkAppN (mkConst ``Lean.Grind.Field.NormNum.ofRat [uA]) #[A, fieldAInst, toExpr q]

private def mkCoeffExpr (A : Expr) (q : Rat) : TacticM Expr := do
  if A.isConstOf ``Rat then
    pure (toExpr q)
  else if q.den == 1 then do
    let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
    let ringAType := mkApp (mkConst ``Lean.Grind.Ring [uA]) A
    let ringAInst ← synthInstance ringAType
    let intCastInst := mkApp2 (mkConst ``Lean.Grind.Ring.intCast [uA]) A ringAInst
    pure <| mkAppN (mkConst ``IntCast.intCast [uA]) #[A, intCastInst, toExpr q.num]
  else
    mkOfRatExpr A q

private def mkReflectCoeffExpr (A : Expr) (q : Rat) : TacticM Expr := do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
  let ratType := mkConst ``Rat
  let commSemiringRatType := mkApp (mkConst ``Lean.Grind.CommSemiring [.zero]) ratType
  let commSemiringRatInst ← synthInstance commSemiringRatType
  let semiringAType := mkApp (mkConst ``Lean.Grind.Semiring [uA]) A
  let semiringAInst ← synthInstance semiringAType
  let algebraRatAType := mkAppN (mkConst ``Lean.Grind.Algebra [.zero, uA])
    #[ratType, A, commSemiringRatInst, semiringAInst]
  let algebraRatAInst ← synthInstance algebraRatAType
  pure <| mkAppN (mkConst ``Lean.Grind.algebraMap [.zero, uA])
    #[ratType, A, commSemiringRatInst, semiringAInst, algebraRatAInst, toExpr q]

private def mkZeroOf (A : Expr) : TacticM Expr := do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
  let zeroType := mkApp (mkConst ``Zero [uA]) A
  let zeroInst ← synthInstance zeroType
  pure <| mkApp2 (mkConst ``Zero.zero [uA]) A zeroInst

private def mkOneOf (A : Expr) : TacticM Expr := do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
  let oneType := mkApp (mkConst ``One [uA]) A
  let oneInst ← synthInstance oneType
  pure <| mkApp2 (mkConst ``One.one [uA]) A oneInst

private def mkWeightedSqProof (A : Expr) (w : Nat) (qExpr : Expr) : TacticM Expr := do
  if A.isConstOf ``Rat then
    mkAppM ``Macaulean.SumOfSquares.weightedSq_nonnegRat #[mkNatLit w, qExpr]
  else
    mkAppM ``Macaulean.SumOfSquares.weightedSq_nonneg #[mkNatLit w, qExpr]

private def mkSqNonnegProof (A qExpr : Expr) : TacticM Expr := do
  let sqExpr ← mkPow qExpr 2
  let goalType ← mkAppM ``LE.le #[← mkZeroOf A, sqExpr]
  proveByTactic goalType (← `(tactic| exact Lean.Grind.OrderedRing.sq_nonneg))

private def mkFinalNonnegProof (A : Expr) (natPosProof hScaledProof : Expr) : TacticM Expr := do
  if A.isConstOf ``Rat then
    mkAppM ``Macaulean.SumOfSquares.nonneg_of_natScale_nonnegRat #[natPosProof, hScaledProof]
  else
    mkAppM ``Macaulean.SumOfSquares.nonneg_of_natScale_nonneg #[natPosProof, hScaledProof]

private def mkScaledCongrProof (A scaleExpr polyEqProof : Expr) : TacticM Expr := do
  let scaledPred ← withLocalDeclD `t A fun t => do
    mkLambdaFVars #[t] (← mkMul scaleExpr t)
  mkAppM ``congrArg #[scaledPred, polyEqProof]

private unsafe def monomialToExpr (A : Expr) (vars : Array Expr) (mon : MRDI.Monomial) :
    TacticM Expr := do
  let mut acc? : Option Expr := none
  for pw in mon.toList do
    let some x := vars[pw.x]? | throwError m!"certificate references missing variable x{toString pw.x}"
    let powExpr ←
      if pw.k == 1 then
        pure x
      else
        mkPow x pw.k
    acc? ← match acc? with
      | none => pure (some powExpr)
      | some acc => pure (some (← mkMul acc powExpr))
  match acc? with
  | some acc => pure acc
  | none => mkOneOf A

private unsafe def termToExpr (mkCoeff : Expr → Rat → TacticM Expr)
    (A : Expr) (vars : Array Expr) (term : MRDI.Term) : TacticM Expr := do
  if term.coeff == 0 then
    mkZeroOf A
  else if term.mon.isEmpty then
    mkCoeff A (term.coeff : Rat)
  else
    let monExpr ← monomialToExpr A vars term.mon
    if term.coeff == 1 then
      pure monExpr
    else if term.coeff == -1 then
      mkAppM ``Neg.neg #[monExpr]
    else
      mkMul (← mkCoeff A (term.coeff : Rat)) monExpr

private unsafe def polyDataToExpr (mkCoeff : Expr → Rat → TacticM Expr)
    (A : Expr) (vars : Array Expr) (poly : MRDI.PolynomialData) : TacticM Expr := do
  let mut acc? : Option Expr := none
  for term in poly.toList do
    if term.coeff != 0 then
      let termExpr ← termToExpr mkCoeff A vars term
      acc? ← match acc? with
        | none => pure (some termExpr)
        | some acc => pure (some (← mkAdd acc termExpr))
  match acc? with
  | some acc => pure acc
  | none => mkZeroOf A

private unsafe def summandToExpr (mkCoeff : Expr → Rat → TacticM Expr)
    (A : Expr) (vars : Array Expr) (summand : SosSummand) : TacticM Expr := do
  let qExpr ← polyDataToExpr mkCoeff A vars summand.poly
  let sqExpr ← mkPow qExpr 2
  if summand.weight == 0 then
    mkZeroOf A
  else if summand.weight == 1 then
    pure sqExpr
  else
    mkMul (← mkCoeff A (summand.weight : Rat)) sqExpr

private unsafe def buildSosExprAndProof (mkCoeff : Expr → Rat → TacticM Expr)
    (A : Expr) (vars : Array Expr) (summands : Array SosSummand)
    (start : Nat := 0) : TacticM (Expr × Expr) := do
  if h : start < summands.size then
    let summand := summands[start]
    let termExpr ← summandToExpr mkCoeff A vars summand
    let qExpr ← polyDataToExpr mkCoeff A vars summand.poly
    let termProof ←
      if summand.weight == 1 then
        mkSqNonnegProof A qExpr
      else
        mkWeightedSqProof A summand.weight qExpr
    if hTail : start + 1 < summands.size then
      let (tailExpr, tailProof) ← buildSosExprAndProof mkCoeff A vars summands (start + 1)
      let sumExpr ← mkAdd termExpr tailExpr
      let sumProof ←
        if A.isConstOf ``Rat then
          mkAppM ``Rat.add_nonneg #[termProof, tailProof]
        else
          mkAppM ``Macaulean.SumOfSquares.add_nonneg #[termProof, tailProof]
      pure (sumExpr, sumProof)
    else
      pure (termExpr, termProof)
  else
    let zeroExpr ← mkZeroOf A
    let zeroProof ← mkAppM ``Macaulean.SumOfSquares.zero_nonneg #[zeroExpr]
    pure (zeroExpr, zeroProof)

private def getGoalPolyExpr? (target : Expr) : MetaM (Option Expr) := do
  match_expr target with
  | LE.le _ _ lhs rhs =>
    let some lhsVal ← evalRatExpr? lhs | pure none
    if lhsVal == 0 then pure (some rhs) else pure none
  | _ => pure none

private def getWitnessPolyExpr? (target : Expr) : MetaM (Option Expr) := do
  let target ← whnf target
  if target.getAppFn.constName? == some ``Macaulean.SumOfSquares.SosWitness then
    pure target.getAppArgs.back?
  else
    pure none

private unsafe def buildWitnessExpr (origPolyExpr : Expr) : TacticM Expr := withMainContext do
  let A ← inferType origPolyExpr
  let (polyExpr, polyEqProof) ← preprocessSosExpr origPolyExpr
  let (poly, reflectedVars) ← Macaulean.AlgPoly.Reify.evalCoeffPoly polyExpr
  let cleared ← clearReflectedPoly poly reflectedVars
  let m2Server ← globalM2Server
  let cert ← m2Server.sosCertificateData cleared.vars.size cleared.polyData
  unless cert.ok do
    throwError m!"m2sos failed: {cert.status}"
  if cert.scale == 0 then
    throwError "m2sos returned an invalid zero scale"
  let totalScale := cleared.scale * cert.scale
  let natPosType ← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit totalScale]
  let natPosProof ← proveByTactic natPosType (← `(tactic| decide))
  if A.isConstOf ``Rat then do
    let (sosExpr, sosProof) ← buildSosExprAndProof mkCoeffExpr A cleared.vars cert.summands
    let scaleExpr ← mkCoeffExpr A (totalScale : Rat)
    let scaledPreExpr ← mkMul scaleExpr polyExpr
    let hEqType ← mkEq scaledPreExpr sosExpr
    let hEqPreProof ← proveByTactic hEqType (← `(tactic| grind))
    let hEqOrigScaled ← mkScaledCongrProof A scaleExpr polyEqProof
    let hEqProof ← mkAppM ``Eq.trans #[hEqOrigScaled, hEqPreProof]
    mkAppM ``Macaulean.SumOfSquares.SosWitness.mk
      #[mkNatLit totalScale, natPosProof, sosExpr, sosProof, hEqProof]
  else
    let (sosExpr, sosProof) ← buildSosExprAndProof mkReflectCoeffExpr A cleared.vars cert.summands
    let scaleExpr ← mkReflectCoeffExpr A (totalScale : Rat)
    let scaledPreExpr ← mkMul scaleExpr polyExpr
    let hEqType ← mkEq scaledPreExpr sosExpr
    let hEqPreProof ←
      try
        proveByTactic hEqType (← `(tactic| algebra_norm))
      catch _ =>
        proveByTactic hEqType (← `(tactic| grind))
    let hEqOrigScaled ← mkScaledCongrProof A scaleExpr polyEqProof
    let hEqProof ← mkAppM ``Eq.trans #[hEqOrigScaled, hEqPreProof]
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
      `(show Macaulean.SumOfSquares.SosWitness _ $p from by
          m2sos_witness)

elab "m2sos" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some polyExpr ← getGoalPolyExpr? target
    | throwTacticEx `m2sos goal
        "expected a goal of the form `0 ≤ p` over a linearly ordered field with a `Rat`-algebra structure"
  let witnessExpr ← unsafe buildWitnessExpr polyExpr
  let finalProof ← mkAppM ``Macaulean.SumOfSquares.SosWitness.proves_nonneg #[witnessExpr]
  goal.assign finalProof
  setGoals ((← getGoals).erase goal)

end Macaulean.SumOfSquares
