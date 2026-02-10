import Lean
import MRDI.Basic
import MRDI.Poly
import Macaulean.Macaulay2
open Lean Grind Elab Tactic Meta

structure VariableState where
  varTable : FVarIdMap CommRing.Var
  coefficientTable : Std.HashMap Lean.Expr CommRing.Var --equality of expressions is probably wrong
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

--TODO this might need to be in MetaM eventually?
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
      let coefficients : Array (String × R) ← coeffArray.mapM <| fun c => do
        match c with
        | .arr #[i, r] =>
          pure (← i.getStr?, ← MrdiType.decode? (α := R) r)
        | _ => throw "Expected a pair of an index and a rational number"
      let poly ← getRef polyUuid
      pure {
        poly := poly
        --TODO deal with the failure case of toNat
        coefficients := .ofArray <| coefficients.map (fun (i,c) => (i.toNat!, c))
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

def intAsRingElem (ringExpr : Expr) (k : Int) : MetaM Expr := do
  let (.some e) ← coerce? (toExpr k) ringExpr | throwError "Invalid Ring"
  pure e


-- This shouldn't be an instance of ToExpr because it's not the expression
-- that realizes the object p.
def exprFromPoly (ringExpr : Expr) (variables : Std.TreeMap CommRing.Var Expr) (exprPoly : ExprPoly) : MetaM Expr :=
  expandPoly exprPoly.poly
  where
    monomialExpr (v : CommRing.Mon) : MetaM Expr :=
      match v with
      | .unit => mkAppOptM ``OfNat.ofNat #[ringExpr, Expr.lit <| Literal.natVal 1, none]
      | .mult ⟨x, k⟩ m => do
        let some varExpr := (variables.get? x) <|> (exprPoly.coefficients.get? x)
          | throwError "Invalid Polynomial"
        let varPower ←
          match k with
          | 1 => pure varExpr
          | _ => mkAppM ``HPow.hPow #[varExpr, toExpr k]
        --avoid extraneous 1's at the end of the term
        match m with
        | .unit => pure <| varPower
        | _ => mkMul varPower (← monomialExpr m)
    expandPoly (p : CommRing.Poly) : MetaM Expr := do
      match p with
      | .num k => intAsRingElem ringExpr k
      | .add k m p' => do
        let tailPoly ← expandPoly p'
        let term ← mkMul (← intAsRingElem ringExpr k) (← monomialExpr m)
        mkAdd term tailPoly

/--
  This structure is simply to capture the return from the Macaulay2 request
  "quotientRemainder"
-/
structure QuotientRemainder where
  quotient : List Mrdi
  remainder : Mrdi
  deriving FromJson, ToJson

-- TODO implement this, for now this returns the ideal as a wrong but correctly
-- formated response so that the code can be tested
def m2IdealMembership
  (I : List Mrdi)
  (f : Mrdi) :
  IO (Except String (List Mrdi)) := do
    let server ← globalM2Server
    let reply : Json ← server.sendRequest "quotientRemainder" (f, I)
    match (fromJson? reply : Except String QuotientRemainder) with
    | .error e =>
      pure <| .error e
    | .ok v =>
      pure <| .ok v.quotient

syntax (name := m2idealmem) "m2idealmem" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

/--
This function implements the core of the tactic, serializing and deserializing
the polynomials to Macaulay2. `ring` should be an expression for the ring
`idealExprs` should be a list of generators for the ideal and `polyExpr` should be
the candidate polynomial. The returned list of expressions is a list of
coefficients such that the product with the generators in idealExprs gives polyExpr
-/
unsafe def m2IdealMemTacticImpl (goal : MVarId) (ring : Expr) (idealExprs : Array Expr) (polyExpr : Expr)
  : MetaM (List Expr) := do
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
  let serializerExpr ← mkAppOptM ``serializePoly #[ring, none]
  let serializerType ← inferType serializerExpr
  let serializer ← evalExpr (ExprPoly → MrdiT MetaM (Option Mrdi)) serializerType serializerExpr DefinitionSafety.unsafe
  let deserializerExpr ← mkAppOptM ``deserializePoly #[ring, none, none]
  let deserializerType ← inferType deserializerExpr
  let deserializer ← evalExpr (Mrdi → MrdiT MetaM (Except String ExprPoly)) deserializerType deserializerExpr DefinitionSafety.unsafe
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
    let .ok result ← m2IdealMembership serializedGens.toList serializedPoly
      | throwTacticEx `m2idealmem goal "Ideal membership failed"
    --deserialize the result
    let deserializedCoefficients ← ExceptT.run do
      let coefficients ← result.mapM deserializer
      coefficients.mapM (liftM ∘ exprFromPoly ring (.ofList varTable))
    match deserializedCoefficients with
    | .ok c => pure c
    | .error e => throwTacticEx `m2idealmem goal e

@[tactic m2idealmem]
unsafe def m2IdealMemTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| m2idealmem [$args,*]) =>
    --TODO rewrite the goals/hypotheses so that they are of the form f = 0
    let goal ← getMainGoal
    let target ← getMainTarget
    let gens ← args.getElems.mapM (fun g => do
      match (← elabTerm g none) with
      | .fvar var =>
        let varDec ← var.getDecl
        pure <| varDec.type
      | e => pure <| e)
    let some (targetRing,targetLhs,targetRhs) := target.eq? |
      throwTacticEx `m2idealmem goal "Expected an equality for the target"
    let zeroExpr ← intAsRingElem targetRing 0
    if not (← isDefEq targetRhs zeroExpr) then
      throwTacticEx `m2idealmem goal "Expected an equaltiy of the form ...=0 for the target"
    let targetPoly := targetLhs
    let genPolys ← gens.mapM (fun e => do
      let (ring,lhs,rhs) := (e.eq?).get!
      if (← isDefEq targetRing ring) && (← isDefEq rhs zeroExpr)
      then pure <| lhs
      else throwTacticEx `m2idealmem goal "Expected equalities to zero over the same ring")
    let coeffs ← m2IdealMemTacticImpl goal targetRing genPolys targetPoly
    let expectedTarget ←
      liftM <| List.foldlM
        mkAdd
        zeroExpr
        (← liftM <| List.zipWithM mkMul coeffs genPolys.toList)
    logInfo expectedTarget
    let equalityGoal ← mkEq expectedTarget targetPoly
    let eqGoalExpr ← mkFreshExprMVar equalityGoal
    logInfo equalityGoal
    let rewriteResult ← goal.rewrite target eqGoalExpr (symm := true)
    let newGoal ← goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
    --use the hypotheses to simplify the lhs of newGoal
    let reducedGoal : MVarId ← liftM <| args.getElems.foldlM (fun goal gen => do
      let genExpr ← elabTerm gen none
      --FIXME this might rewrite too much and cause later rewrites to fail
      let rewriteResult ← goal.rewrite (← goal.getType) genExpr
      goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
      )
      newGoal
    -- For now at least, we just call grind to prove reducedGoal
    -- reducedGoal is basically just `0 = 0`, so we should be able
    -- to do it more directly
    _ ← runTactic reducedGoal (← `(tactic|grind))
    --use grind to prove the equality
    _ ← runTactic eqGoalExpr.mvarId! (← `(tactic|grind))
    -- set the goal to the polynomial equality
    -- TODO prove this ourselves
    -- setGoals [eqGoalExpr.mvarId!]
  | _ => throwTacticEx `m2idealmem (← getMainGoal) "Expect list of equalities for the ideal"
