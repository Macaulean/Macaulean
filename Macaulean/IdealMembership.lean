import Lean
import MRDI.Basic
import MRDI.Poly
import Macaulean.Macaulay2
import Macaulean.Grind.Algebra.Instances
import Macaulean.Grind.AlgPoly.Kronecker
import Macaulean.Grind.AlgPoly.Reify
open Lean Grind Elab Parser Tactic Meta

structure VariableState where
  varTable : FVarIdMap CommRing.Var
  -- Equality of expressions is suboptimal but will work for now
  coefficientTable : Std.HashMap Lean.Expr CommRing.Var
  nextVar : CommRing.Var

def VariableState.mapVariable (state : VariableState) (var : FVarId) :
  CommRing.Var × VariableState :=
  let (optVar, newTable) := state.varTable.getThenInsertIfNew? var state.nextVar
  match optVar with
  | .some v => (v, state)
  | .none => (state.nextVar, {
      state with
        varTable := newTable
        nextVar := state.nextVar + 1})

def VariableState.mapCoefficient (state : VariableState) (x : Lean.Expr) :
  (CommRing.Var × VariableState) :=
  let (optVar, newTable) := state.coefficientTable.getThenInsertIfNew? x state.nextVar
  match optVar with
  | .some v => (v, state)
  | .none => (state.nextVar, {
      state with
        coefficientTable := newTable
        nextVar := state.nextVar + 1 })

def VariableState.empty : VariableState := {
  varTable := .empty
  coefficientTable := .emptyWithCapacity
  nextVar := .zero
}

--TODO flesh this out
class Macaulay2Ring (R : Type) extends MrdiType R where
  mrdiDesc : IO Json
  fromLitExpr? : Expr → MetaM (Option R)

structure RingInfo where
  ringName : String
  toMrdi? : Expr → MetaM (Option Json)

--this should probably be in MRDI.Basic
instance : MrdiType Int where
  mrdiType := .string "Int"
  decode? := trivialDecode?
  encode := trivialEncode

instance : MrdiType Rat where
  mrdiType := .string "Rat"
  decode? (x : Json) := do
    let .ok ((nstr, dstr) : String × String) := fromJson? x | return .error "Expected a pair"
    let some num := nstr.toInt? | return .error "Expect an integer numerator"
    let some den := dstr.toNat? | return .error "Expected a non-negative denominator"
    if den = 0
    then pure <| .error "Expected a non-zero denominator"
    else pure <| .ok <| mkRat num den
  encode (x : Rat) := pure <| .arr #[toString x.num, toString x.den]

instance : Macaulay2Ring Int where
  mrdiDesc := pure <| .str "Int" --TODO actually think about this representation
  fromLitExpr? := getIntValue?

instance : Macaulay2Ring Rat where
  mrdiDesc := pure <| .str "Rat"
  fromLitExpr? := getRatValue?

structure ConcretePoly (R : Type) where
  poly : CommRing.Poly
  coefficients : Std.TreeMap CommRing.Var R

instance [Repr R] : Repr (ConcretePoly R) where
  reprPrec x _ := f!"{repr x.poly} {repr x.coefficients}"

instance [BEq R] : BEq (ConcretePoly R) where
  beq x y := (x.poly == y.poly) && (x.coefficients.toList == y.coefficients.toList)


unsafe instance [MrdiType R] : MrdiType (ConcretePoly R) where
  --TODO this should really be a parameterized mrdiType, but those require better UUID infrastructure
  mrdiType := .parameterized "ConcretePoly" (.str <| toString <| MrdiType.mrdiType (α := R))
  decode? (x : Json) := ExceptT.run <| do
    match x with
    | .obj fields =>
      let some (.str polyUuid) := fields.get? "poly" | throw "Expected a JSON object with a 'poly' field"
      let some polyUuid := toUuid? polyUuid | throw "Expect a reference for the 'poly' field"
      let some (.arr coeffArray) := fields.get? "coefficients" | throw "Expected a JSON object with a 'coefficients' field"
      let coefficients : Array (Nat × R) ← coeffArray.mapM <| fun c => do
        match c with
        | .arr #[i, r] =>
          let istr ← i.getStr?
          let some inat := istr.toNat? | throw s!"Expected a String representing a Nat {istr}"
          pure (inat, ← MrdiType.decode? (α := R) r)
        | _ => throw "Expected a pair of an index and a rational number"
      let poly ← getRef polyUuid
      pure {
        poly := poly
        --TODO deal with the failure case of toNat
        coefficients := .ofArray coefficients
      }
    | _ => throw "Expected a JSON object"
  --TODO use UUID's and references to do this properly
  encode (p : ConcretePoly R) := do
    let basePolyUuid ← addReference p.poly
    let coefficients ← p.coefficients.toArray.mapM (fun (i,x) => (toString i, ·) <$> MrdiType.encode x)
    pure <| Json.mkObj [
      ("poly", toJson basePolyUuid),
      ("coefficients", .arr <| coefficients.map toJson) ]

structure ExprPoly where
  poly : CommRing.Poly
  coefficients : Std.TreeMap Nat Expr
  deriving Inhabited, Repr

unsafe def serializePoly [Macaulay2Ring R] (p : ExprPoly)
  : MrdiT MetaM (Option Mrdi) := OptionT.run do
  let convertedCoefficients : List (Nat × R) ←
    p.coefficients.toList.mapM (fun (i,x) => do
      let x' ← OptionT.mk <| Macaulay2Ring.fromLitExpr? x
      pure (i, x'))
  let concretePoly : ConcretePoly R := {
    poly := p.poly
    coefficients :=  Std.TreeMap.ofList convertedCoefficients }
  OptionT.lift <| toMrdi concretePoly

unsafe def deserializePoly [ToExpr R] [Macaulay2Ring R] (polyMrdi : Mrdi)
  : MrdiT MetaM (Except String ExprPoly) := ExceptT.run do
  let poly : ConcretePoly R ← fromMrdi? polyMrdi
  let exprCoefficients  := poly.coefficients.map (fun _ x => toExpr x)
  pure {
    poly := poly.poly
    coefficients := exprCoefficients
  }

--inspired by Grind.Arith.CommRing.reify?
partial def toCommRingExpr?
  (x : Lean.Expr)
  : StateT VariableState MetaM (Option CommRing.Expr) := OptionT.run do
  match_expr x with
  --TODO: figure out what we need to be careful about with types
  | HAdd.hAdd _ _ _ _ a b =>
    .add <$> (toCommRingExpr? a) <*> (toCommRingExpr? b)
  | HMul.hMul _ _ _ _ a b =>
    .mul <$> (toCommRingExpr? a) <*> (toCommRingExpr? b)
  | HSub.hSub _ _ _ _ a b =>
    .sub <$> (toCommRingExpr? a) <*> (toCommRingExpr? b)
  | HPow.hPow _ _ _ _ a b =>
    .pow <$> (toCommRingExpr? a) <*> (OptionT.mk <| getNatValue? b)
  -- | HDiv.hDiv _ _ _ _ a b => pure <| none
  --^ TODO actually implement, should work if b is an element of R and R is a field
  | OfNat.ofNat _ x _ =>
    let n ← OptionT.mk <| getNatValue? x
    pure <| .num <| .ofNat n
  | Neg.neg _ _ a =>
    CommRing.Expr.neg <$> toCommRingExpr? a
  | _ =>
    match x with
    | .fvar varId =>
      let varName ← modifyGet (
        fun varState => varState.mapVariable varId)
      pure <| .var varName
    | _ =>
      -- TODO in this case we should check that x doesn't contain any variables
      let varName ← modifyGet (
        fun varState => varState.mapCoefficient x)
      pure <| .var varName

def toExprPoly (p : CommRing.Poly) : StateT VariableState MetaM (ExprPoly) := do
  let state ← get
  let coeff := Std.TreeMap.ofList <| state.coefficientTable.toList.map Prod.swap
  pure {
    poly := p
    coefficients := coeff
  }

def natAsRingElem (ringExpr : Expr) (k : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[ringExpr, mkRawNatLit k, none]

def intAsRingElem (ringExpr : Expr) (k : Int) : MetaM Expr := do
  let a := k.natAbs
  let aExpr ← natAsRingElem ringExpr a
  if k >= 0
  then pure aExpr
  else mkAppM ``Neg.neg #[aExpr]

-- This shouldn't be an instance of ToExpr because it's not the expression
-- that realizes the object p.
def exprFromPoly (ringExpr : Expr)
  (variables : Std.TreeMap CommRing.Var Expr)
  (exprPoly : ExprPoly) (reindex : Bool := true) : MetaM Expr := do
  expandPoly none exprPoly.poly
  where
    varList := variables.keys.mergeSort.toArray
    monomialExpr (currExpr : Option Expr) (v : CommRing.Mon) : MetaM Expr := do
      match v with
      | .unit => pure <| currExpr.getD (← natAsRingElem ringExpr 1)
      | .mult ⟨x, k⟩ m => do
        -- Macaulay2 returns the variables in the same order but as the first
        -- variables of the poly field, this reindexes.
        -- We should probably use a more purpose built polynomial type to avoid this
        -- In particular, we should probably just have a polynomial that deals with
        -- coefficients separately
        let x' := if reindex then varList[x]? else some x
        let some varExpr := (x' >>= variables.get?) <|> (exprPoly.coefficients.get? x)
          | throwError s!"Invalid variable index {x} exceeds the number of variables {varList.size}"
        let varPower ←
          match k with
          | 1 => pure varExpr
          | _ => mkAppM ``HPow.hPow #[varExpr, mkNatLit k]
        match currExpr with
        | none => monomialExpr varPower m
        | some e => monomialExpr (← mkMul e varPower) m
    expandPoly (currExpr : Option Expr) (p : CommRing.Poly) : MetaM Expr := do
      match p with
      | .num k =>
        let newTerm ← intAsRingElem ringExpr k
        match currExpr with
        | none => pure newTerm
        | some expr =>
          if k == 0
          then pure expr --avoid the trailing zero
          else mkAdd expr newTerm
      | .add k m p' => do
        let coeff ← intAsRingElem ringExpr k
        let term ← monomialExpr (if k == 1 then none else some coeff) m
        let newExpr ← match currExpr with
        | none => pure term
        | some expr => mkAdd expr term
        expandPoly newExpr p'

/--
  This structure is simply to capture the return from the Macaulay2 request
  "quotientRemainder"
-/
structure QuotientRemainder where
  quotient : List Mrdi
  remainder : Mrdi
  deriving FromJson, ToJson

def m2QuotientRemainder
  (I : List Mrdi)
  (f : Mrdi) :
  IO (Except String (QuotientRemainder)) := do
    let server ← globalM2Server
    let reply : Json ← server.sendRequest "quotientRemainder" (f, I)
    pure <| fromJson? reply

namespace Macaulean.IdealMembership

structure Config where
  --whether to use grind to prove the final polynomial equalities
  grind : Bool := false
  /-- Close the goal with a kernel-checked linear-combination certificate:
  Macaulay2's cofactors enter the proof as `KPoly` data (never as ring
  syntax), and one `decide +kernel` evaluation of
  `Macaulean.AlgExpr.checkLinComb` verifies `p = Σ qᵢ·gᵢ`. -/
  cert : Bool := false
  deriving Inhabited, Repr

declare_config_elab configElab Config

end Macaulean.IdealMembership

open Macaulean

/--
This function implements the core of the tactic, serializing and deserializing
the polynomials to Macaulay2. `ring` should be an expression for the ring
`idealExprs` should be a list of generators for the ideal and `polyExpr` should be
the candidate polynomial. Returns the cofactors and the remainder as *data*
(`ExprPoly`), together with the variable table mapping Macaulay2's variables
back to the goal's free variables; `m2QuotientRemainderImpl` below rebuilds
ring expressions from these for the expression-based tactics.
-/
unsafe def m2QuotientRemainderData (goal : MVarId) (ring : Expr) (idealExprs : Array Expr) (polyExpr : Expr)
  : MetaM (List ExprPoly × ExprPoly × List (CommRing.Var × Expr)) := do
  dbg_trace "M2IdealMem Start"
  --parse a expression into a polynomial, checking that the ring matches using isDefEq
  let getPoly (expectedRing : Expr) (pExpr : Expr) : StateT VariableState MetaM ExprPoly := do
    let some poly ← toCommRingExpr? pExpr
      | throwTacticEx `m2idealmem goal "Expected polynomials over the same base ring"
    toExprPoly poly.toPoly
  let getPolys := do
    let some poly ← toCommRingExpr? polyExpr
      | throwTacticEx `m2idealmem goal "Expected a polynomial equality"
    let exprPoly ← toExprPoly poly.toPoly
    let genPolys ← idealExprs.mapM (getPoly ring)
    pure <| some (genPolys, exprPoly)
  let (some (idealGens, poly), vars) ← getPolys.run .empty | throwTacticEx `m2idealmem goal "Expected a polynomial expression"
  let varTable := List.map (fun (v, fvarId) => (v, Expr.fvar fvarId)) <|
    vars.varTable.toList.map Prod.swap

  -- try to build the serializer and deserializer pair, if it fails
  -- try to universalize to ZZ
  let intExpr := mkConst ``Int
  let (serializerExpr,universal) ←
    try
      let expr ← mkAppOptM ``serializePoly #[ring, none]
      pure (expr, false)
    catch _ =>
      let funcExpr ← mkAppOptM ``serializePoly #[intExpr, none]
      pure (funcExpr,true)
  let serializationRing := if universal then intExpr else ring
  let castInstance ← mkAppOptM ``Ring.intCast #[ring,none]
  let incExpr ←
    if universal
    then mkAppOptM ``IntCast.intCast #[ring,castInstance]
    else mkAppOptM ``id #[ring]
  let serializerType ← inferType serializerExpr
  let serializer ← evalExpr (ExprPoly → MrdiT MetaM (Option Mrdi)) serializerType serializerExpr DefinitionSafety.unsafe

  let deserializerExpr ← mkAppOptM ``deserializePoly #[serializationRing, none, none]
  let deserializerType ← inferType deserializerExpr
  let deserializer ← evalExpr (Mrdi → MrdiT MetaM (Except String ExprPoly)) deserializerType deserializerExpr DefinitionSafety.unsafe

  let liftedDeserializer (m : Mrdi) : MrdiT MetaM (Except String ExprPoly) := do
    match ← deserializer m with
    | .ok poly =>
      let liftedCoefficients := poly.coefficients.map (fun _ x => mkApp incExpr x)
      pure <| .ok {
        poly := poly.poly
        coefficients := liftedCoefficients
      }
    | e => pure e
  let s ← IO.rand 0 (2^64-1)
  --I should be able to use the runMrdiIO variant
  -- but I can't get it to infer the right MonadLift instance
  runMrdiWithSeed s do
    --serialize the polynomials
    let some serializedPoly ← serializer poly
      | throwTacticEx `m2idealmem goal "Unable to serialize polynomial"
    let serializedGens : Array (Option Mrdi) ← (idealGens.mapM serializer)
    let some serializedGens := serializedGens.mapM id
      | throwTacticEx `m2idealmem goal "Unable to serialize ideal generators"
    --run Macaulay2
    dbg_trace "Calling Macaulay2"
    let .ok result ← m2QuotientRemainder serializedGens.toList serializedPoly
      | throwTacticEx `m2idealmem goal "Ideal membership failed"
    dbg_trace "Coefficients Returned"
    --deserialize the result
    let deserializedCoefficients ← ExceptT.run <|
      result.quotient.mapM liftedDeserializer
    let deserializedRemainder ← ExceptT.run <|
      liftedDeserializer result.remainder
    match deserializedCoefficients, deserializedRemainder with
    | .ok c, .ok r  => pure (c, r, varTable)
    | .error e, _ => throwTacticEx `m2idealmem goal e
    | _, .error e => throwTacticEx `m2idealmem goal e

/--
Expression-based variant of `m2QuotientRemainderData`: the returned list of
expressions is a list of coefficients such that the product with the
generators in `idealExprs` gives `polyExpr` (up to the returned remainder).
-/
unsafe def m2QuotientRemainderImpl (goal : MVarId) (ring : Expr) (idealExprs : Array Expr) (polyExpr : Expr)
  : MetaM (List Expr × Expr) := do
  let (quotients, remainder, varTable) ← m2QuotientRemainderData goal ring idealExprs polyExpr
  let c ← quotients.mapM (exprFromPoly ring (.ofList varTable))
  let r ← exprFromPoly ring (.ofList varTable) remainder
  pure (c, r)

--TODO rename this
theorem helper [CommRing R] (a b c d : R) (h1 : a = d) (h2 : b = 0) : a+c*b = d := by
  rewrite [h1,h2]
  simp [Semiring.mul_zero,Semiring.add_zero]

-- factor out the core tactic to make the code a bit simpler
-- this only reduces down the the polynomial equality step
unsafe def m2IdealMemTacticRunner (cfg : IdealMembership.Config) (tacName : Name) (goal : MVarId) (target : Expr) (genHyps : Array Expr) : TacticM Unit := do
  let genProps ←  genHyps.mapM (fun genH => inferType genH)
  let some (targetRing,targetLhs,targetRhs) := target.eq? |
      tacticError "Expected an equality for the target"
  let zeroExpr ← natAsRingElem targetRing 0
  if not (← isDefEq targetRhs zeroExpr) then
    tacticError "Expected an equality of the form ...=0 for the target"
  let genPolys ← genProps.mapM (fun e => do
    let .some (ring,lhs,rhs) := e.eq? | tacticError "Expected a list of equalities"
    if (← isDefEq targetRing ring) && (← isDefEq rhs zeroExpr)
    then pure <| lhs
    else tacticError "Expected equalities to zero over the same ring")
  let (coeffs,_) ← m2QuotientRemainderImpl goal targetRing genPolys targetLhs
  dbg_trace "Coefficients Read"
  let startingExpr ← mkEqRefl zeroExpr
  let zeroProof ← (coeffs.zip genHyps.toList).foldlM
    (fun mvar (c,f) => do
      mkAppOptM ``helper #[targetRing, none, none, none, c, zeroExpr, mvar, f])
    startingExpr
  dbg_trace "Vanishing Proven"
  let zeroProofType ← inferType zeroProof
  let some (_,expectedTarget,_) := zeroProofType.eq?
    | tacticError m!"Vanishing Statement Unexpectedly not an equality {zeroProofType}"
  --rewrite the goal using the fact that the previous expression equals zero
  let eqGoalMVar ← mkFreshExprMVar (← mkEq targetLhs expectedTarget)
  if ← goal.checkedAssign (← mkEqTrans eqGoalMVar zeroProof)
  then
    dbg_trace "New Goal Created"
    pushGoals [eqGoalMVar.mvarId!]
  else
    tacticError "Failed to show vanishing"
  where
    tacticError {α} (x := none) : TacticM α := throwTacticEx tacName goal x

/--
  This expects goal to be a proposition of the type `g = h` over some ring
  The rhs of this may be a mvar but the lhs should not be. This uses Macaulay2 and the hypotheses in genHyps
  to reduce the lhs fully in grevlex order. then it creates a new goal of the form (remainder) = expr
  the expressions in genHyps should be theorems of the form `f = 0` for a polynoial expression f.
-/
unsafe def m2RemainderTacticRunner (cfg : IdealMembership.Config) (tacName : Name) (goal : MVarId) (target : Expr) (genHyps : Array Expr) : TacticM Unit := do
  let genProps ←  genHyps.mapM (fun genH => inferType genH)
  let some (targetRing,targetLhs,targetRhs) := target.eq? |
      tacticError "Expected an equality for the target"
  let zeroExpr ← natAsRingElem targetRing 0
  let genPolys ← genProps.mapM (fun e => do
    let (ring,lhs,rhs) := (e.eq?).get!
    if (← isDefEq targetRing ring) && (← isDefEq rhs zeroExpr)
    then pure <| lhs
    else tacticError "Expected equalities to zero over the same ring")
  let (coeffs,_) ← m2QuotientRemainderImpl goal targetRing genPolys targetLhs
  dbg_trace "Coefficients Read"
  let startingExpr ← mkEqRefl targetRhs
  let remainderProof ← (coeffs.zip genHyps.toList).foldlM
    (fun mvar (c,f) => do
      mkAppOptM ``helper #[targetRing, none, none, none, c, none, mvar, f])
    startingExpr
  let remainderProofType ← inferType remainderProof
  let some (_,expectedTarget,_) := remainderProofType.eq?
    | tacticError "Impossible"
  let eqGoalMVar ← mkFreshExprMVar (← mkEq targetLhs expectedTarget)
  if ← goal.checkedAssign (← mkEqTrans eqGoalMVar remainderProof)
  then
    dbg_trace "New Goal Created"
    pushGoals [eqGoalMVar.mvarId!]
  else
    tacticError "Failed to show remainder"
  where
    tacticError {α} (x := none) : TacticM α := throwTacticEx tacName goal x

/-! ### Certificate-based ideal membership (cofactors as data)

`m2CertTacticRunner` closes `p = 0` from hypotheses `gᵢ = 0` with a single
kernel computation of `Macaulean.AlgExpr.checkLinComb`: the target and the
generators are reified to `AlgExpr` (their denotations tie back to the goal
by `rfl`), while Macaulay2's cofactors enter the proof term as Kronecker-packed
`KPoly` list literals.  The cofactors are never rebuilt as ring expressions,
so their size costs neither elaboration nor reification — which is what makes
16k-term quotients (`lean4#11861`) representable at all. -/

/-- Tail-recursive listing of a `Poly`'s monomials as `(coeff, [(var, pow)])`;
the trailing constant becomes a monomial with no powers. -/
private def polyMonomialList (p : CommRing.Poly) : List (Int × List (Nat × Nat)) :=
  go p []
where
  monPowers (m : CommRing.Mon) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match m with
    | .unit => acc.reverse
    | .mult pw m => monPowers m ((pw.x, pw.k) :: acc)
  go (p : CommRing.Poly) (acc : List (Int × List (Nat × Nat))) :
      List (Int × List (Nat × Nat)) :=
    match p with
    | .num k => ((if k == 0 then acc else (k, []) :: acc)).reverse
    | .add k m rest => go rest ((k, monPowers m []) :: acc)

unsafe def m2CertTacticRunner (tacName : Name) (goal : MVarId) (target : Expr)
    (genHyps : Array Expr) : TacticM Unit := withMainContext do
  let genProps ← genHyps.mapM (fun genH => inferType genH)
  let some (targetRing, targetLhs, targetRhs) := target.eq? |
    tacticError "Expected an equality for the target"
  let zeroExpr ← natAsRingElem targetRing 0
  unless (← isDefEq targetRhs zeroExpr) do
    tacticError "Expected an equality of the form _ = 0 for the target"
  let genPolys ← genProps.mapM fun (e : Expr) => do
    let some (ring, lhs, rhs) := e.eq? | tacticError "Expected a list of equalities"
    if (← isDefEq targetRing ring) && (← isDefEq rhs zeroExpr)
    then pure lhs
    else tacticError "Expected equalities to zero over the same ring"
  -- Macaulay2 division, results as data
  let (quotData, remData, varTableList) ←
    m2QuotientRemainderData goal targetRing genPolys targetLhs
  dbg_trace "m2 cert: coefficients received"
  -- ideal membership needs a zero remainder
  match remData.poly with
  | .num 0 => pure ()
  | _ => tacticError m!"Macaulay2 remainder is nonzero: the target is not in the ideal \
      generated by the hypotheses"
  -- reify target and generators with one shared atom state
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel targetRing
  let csInst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommSemiring [uA]) targetRing)
  let sInst ← synthInstance (mkApp (mkConst ``Lean.Grind.Semiring [uA]) targetRing)
  let commRingAInst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommRing [uA]) targetRing)
  let ringAInst ← synthInstance (mkApp (mkConst ``Lean.Grind.Ring [uA]) targetRing)
  let algInst := mkApp2 (mkConst ``Lean.Grind.Algebra.selfAlgebra [uA]) targetRing csInst
  let algebraMapFn := mkApp5 (mkConst ``Lean.Grind.algebraMap [uA, uA])
    targetRing targetRing csInst sInst algInst
  let ((pReified, gsReified), rstate) ← (do
      let p ← Macaulean.AlgPoly.Reify.reifyAmbientExpr algebraMapFn targetLhs
      let gs ← genPolys.mapM (Macaulean.AlgPoly.Reify.reifyAmbientExpr algebraMapFn)
      pure (p, gs)).run {}
  -- map Macaulay2's variables to reified atoms (mirrors exprFromPoly's reindexing)
  let vt : Std.TreeMap CommRing.Var Expr := .ofList varTableList
  let varList := vt.keys.mergeSort.toArray
  let ambMap := rstate.ambientVarMap
  -- coefficient atoms: goal-derived ones first, then Macaulay2's rational constants
  let mut coeffVars := rstate.coeffVars
  let mut coeffVarMap := rstate.coeffVarMap
  -- pass 1: classify every cofactor monomial
  -- rawQuots : per cofactor, list of (int coeff, [(ambient idx, pow)], [(coeff idx, pow)])
  let mut rawQuots : Array (Array (Int × List (Nat × Nat) × List (Nat × Nat))) := #[]
  for q in quotData do
    let mut mons : Array (Int × List (Nat × Nat) × List (Nat × Nat)) := #[]
    for (k, pows) in polyMonomialList q.poly do
      let mut realPows : List (Nat × Nat) := []
      let mut coeffPows : List (Nat × Nat) := []
      for (v, pow) in pows do
        match varList[v]? >>= vt.get? with
        | some fvarE =>
          let some idx := ambMap[fvarE]? |
            tacticError m!"certificate variable {fvarE} does not occur in the goal"
          realPows := (idx, pow) :: realPows
        | none =>
          let some cE := q.coefficients.get? v |
            tacticError m!"invalid variable index {v} in Macaulay2 cofactor"
          let cIdx ← match coeffVarMap[cE]? with
            | some i => pure i
            | none =>
              let i := coeffVars.size
              coeffVars := coeffVars.push cE
              coeffVarMap := coeffVarMap.insert cE i
              pure i
          coeffPows := (cIdx, pow) :: coeffPows
      mons := mons.push (k, realPows, coeffPows)
    rawQuots := rawQuots.push mons
  -- choose the Kronecker parameters (guards inside checkLinComb re-check them)
  let algExprTy := mkApp (mkConst ``Macaulean.AlgExpr [.zero]) Macaulean.AlgPoly.Reify.polyType
  let pVal ← evalExpr (Macaulean.AlgExpr CommRing.Poly) algExprTy pReified
  let gVals ← gsReified.mapM fun gE =>
    liftM (evalExpr (Macaulean.AlgExpr CommRing.Poly) algExprTy gE : MetaM _)
  let nv := rstate.ambientVars.size
  let mut dBound := pVal.degBound
  for i in [0:rawQuots.size] do
    let qMax := rawQuots[i]!.foldl (fun acc (_, realPows, _) =>
      realPows.foldl (fun acc (_, pow) => Nat.max acc pow) acc) 0
    let gBound := (gVals[i]?.map Macaulean.AlgExpr.degBound).getD 0
    dBound := Nat.max dBound (qMax + gBound)
  let dBase := dBound + 2
  -- pass 2: build the KPoly values (native) and literals (Expr)
  let natTy := mkConst ``Nat
  let kEntryTy := mkApp2 (mkConst ``Prod [.zero, .zero]) natTy Macaulean.AlgPoly.Reify.polyType
  let kPolyTy := mkApp (mkConst ``List [.zero]) kEntryTy
  let pairTy := mkApp2 (mkConst ``Prod [.zero, .zero]) kPolyTy algExprTy
  let mut qValsAndLits : Array (Macaulean.KPoly CommRing.Poly × Expr) := #[]
  for mons in rawQuots do
    let mut entries : Array ((Nat × CommRing.Poly) × Expr) := #[]
    for (k, realPows, coeffPows) in mons do
      let key := realPows.foldl (fun acc (idx, pow) => acc + pow * dBase ^ idx) 0
      -- coefficient as a grind Poly: k · Π coeffVarᵢ^powᵢ, normalized by toPoly
      let coeffExpr : CommRing.Expr := coeffPows.foldl
        (fun acc (cIdx, pow) => .mul acc (.pow (.var cIdx) pow)) (.num k)
      let coeffPoly := coeffExpr.toPoly
      entries := entries.push ((key, coeffPoly),
        mkApp4 (mkConst ``Prod.mk [.zero, .zero]) natTy Macaulean.AlgPoly.Reify.polyType
          (mkRawNatLit key) (Macaulean.AlgPoly.Reify.mkPolyValueExpr coeffPoly))
    -- sort by key ascending so the merge-based kernel ops stay near-linear
    let sorted := entries.qsort (fun a b => a.1.1 < b.1.1)
    let qVal := sorted.toList.map (·.1)
    let qLit := sorted.foldr
      (fun e acc => mkApp3 (mkConst ``List.cons [.zero]) kEntryTy e.2 acc)
      (mkApp (mkConst ``List.nil [.zero]) kEntryTy)
    qValsAndLits := qValsAndLits.push (qVal, qLit)
  -- native pre-check before any kernel work
  let pairsVal := (qValsAndLits.toList.map (·.1)).zip (gVals.toList)
  unless Macaulean.AlgExpr.checkLinComb dBase nv pVal pairsVal [] do
    tacticError m!"linear-combination certificate check failed natively \
      (base {dBase}, {nv} variables) — this usually indicates a variable-mapping bug"
  dbg_trace "m2 cert: native check passed (base {dBase}, {nv} vars)"
  -- Expr-level certificate pieces
  let pairsLit := (qValsAndLits.zip gsReified).foldr
    (fun ((_, qLit), gE) acc =>
      mkApp3 (mkConst ``List.cons [.zero]) pairTy
        (mkApp4 (mkConst ``Prod.mk [.zero, .zero]) kPolyTy algExprTy qLit gE) acc)
    (mkApp (mkConst ``List.nil [.zero]) pairTy)
  let rNil := mkApp (mkConst ``List.nil [.zero]) kEntryTy
  let coeffCtx ← Macaulean.AlgPoly.Reify.mkContextExpr targetRing coeffVars
  let ambientCtx ← Macaulean.AlgPoly.Reify.mkContextExpr targetRing rstate.ambientVars
  let coeffRingPolyInst ← synthInstance
    (mkApp (mkConst ``Macaulean.CoeffRing [.zero]) Macaulean.AlgPoly.Reify.polyType)
  let commRingRInst := commRingAInst
  let phi := mkLambda `p .default Macaulean.AlgPoly.Reify.polyType <|
    mkApp algebraMapFn <|
      mkAppN (mkConst ``Lean.Grind.CommRing.Poly.denote [uA])
        #[targetRing, ringAInst, coeffCtx, mkBVar 0]
  let hphi := mkAppN (mkConst ``Macaulean.AlgPoly.Reify.polyCoeffIsRingHom)
    #[targetRing, targetRing, commRingRInst, commRingAInst, algInst, coeffCtx]
  -- rfl bridges: denote of a reified expression is the source expression
  let denoteOf (e : Expr) : Expr :=
    mkAppN (mkConst ``Macaulean.AlgExpr.denote [.zero, uA])
      #[Macaulean.AlgPoly.Reify.polyType, targetRing, commRingAInst, phi, ambientCtx, e]
  let proveRfl (lhs rhs : Expr) : TacticM Expr := do
    let mvar ← mkFreshExprMVar (← mkEq lhs rhs)
    let savedGoals ← getGoals
    setGoals [mvar.mvarId!]
    try
      evalTactic (← `(tactic| rfl))
    finally
      setGoals savedGoals
    instantiateMVars mvar
  -- ZeroGens: each generator denotes to zero, via its bridge and hypothesis
  let mut hz : Expr := mkConst ``True.intro
  for i in [0:gsReified.size] do
    let j := gsReified.size - 1 - i
    let bridge ← proveRfl (denoteOf gsReified[j]!) genPolys[j]!
    let comp ← mkEqTrans bridge genHyps[j]!
    hz ← mkAppM ``And.intro #[comp, hz]
  -- the kernel-checked certificate
  let checkApp := mkAppN (mkConst ``Macaulean.AlgExpr.checkLinComb [.zero])
    #[Macaulean.AlgPoly.Reify.polyType, coeffRingPolyInst,
      mkRawNatLit dBase, mkRawNatLit nv, pReified, pairsLit, rNil]
  let hChkMVar ← mkFreshExprMVar (← mkEq checkApp (mkConst ``true))
  let savedGoals ← getGoals
  setGoals [hChkMVar.mvarId!]
  try
    evalTactic (← `(tactic| decide +kernel))
  finally
    setGoals savedGoals
  let hChk ← instantiateMVars hChkMVar
  dbg_trace "m2 cert: kernel check done"
  let core := mkAppN (mkConst ``Macaulean.AlgExpr.eq_of_checkLinComb [.zero, uA])
    #[Macaulean.AlgPoly.Reify.polyType, targetRing, coeffRingPolyInst, commRingAInst,
      phi, ambientCtx, hphi, mkRawNatLit dBase, mkRawNatLit nv,
      pReified, pairsLit, rNil, hz, hChk]
  let pBridge ← proveRfl (denoteOf pReified) targetLhs
  let proof ← mkEqTrans (← mkEqSymm pBridge) core
  if ← goal.checkedAssign proof then
    dbg_trace "m2 cert: goal closed"
  else
    tacticError "certificate proof failed to close the goal"
  where
    tacticError {α} (x := none) : TacticM α := throwTacticEx tacName goal x

syntax (name := m2idealmem) "m2idealmem" optConfig notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic m2idealmem]
unsafe def m2IdealMemTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| m2idealmem $optCfg [$args,*]) =>
    let cfg ← IdealMembership.configElab optCfg
    let goal ← getMainGoal
    let target ← getMainTarget
    let genHyps ← args.getElems.mapM (elabTerm · none)
    if cfg.cert then
      m2CertTacticRunner `m2idealmem goal target genHyps
      dbg_trace "m2idealmem finished"
      return
    m2IdealMemTacticRunner cfg `m2idealmem goal target genHyps
    if cfg.grind
    then
      _ ← runTactic (← getMainGoal) (← `(tactic|grind))
      dbg_trace "Equality Shown"
    dbg_trace "m2idealmem finished"
  | _ => throwTacticEx `m2idealmem (← getMainGoal) "Expect list of equalities for the ideal"

syntax (name := m2remainder) "m2remainder" optConfig notFollowedBy("|") (ppSpace colGt term:max)* : tactic

@[tactic m2remainder]
unsafe def m2RemainderTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| m2remainder $optCfg [$args,*]) =>
    let cfg ← IdealMembership.configElab optCfg
    let goal ← getMainGoal
    let target ← getMainTarget
    let genHyps ← args.getElems.mapM (elabTerm · none)
    m2RemainderTacticRunner cfg `m2remainder goal target genHyps
    if cfg.grind
    then
      _ ← runTactic (← getMainGoal) (← `(tactic|grind))
      dbg_trace "Equality Shown"
    dbg_trace "m2idealmem finished"
  | _ => throwTacticEx `m2idealmem (← getMainGoal) "Expect list of equalities for the ideal"
