import Lean
import MRDI.Basic
import MRDI.Poly
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
  : MrdiT TacticM (Option Mrdi) := OptionT.run do
  let convertedCoefficients : List (Nat × R) ←
    p.coefficients.toList.mapM (fun (i,x) => do
      let x' ← OptionT.mk <| Macaulay2Ring.fromLitExpr? x
      pure (i, x'))
  let concretePoly : ConcretePoly R := {
    poly := p.poly
    coefficients :=  Std.TreeMap.ofList convertedCoefficients }
  OptionT.lift <| toMrdi concretePoly

unsafe def deserializePoly [ToExpr R] [Macaulay2Ring R] (polyMrdi : Mrdi)
  : MrdiT TacticM (Except String ExprPoly) := ExceptT.run do
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

def eqExprToPoly
  (expr : Expr)
  : StateT VariableState MetaM (Option (Expr × CommRing.Poly)) := OptionT.run do
  let (ring,lhs,rhs) ← liftOption expr.eq?
  let polyExpr : CommRing.Expr ←
    .sub <$> (toCommRingExpr? lhs) <*> (toCommRingExpr? rhs)
  pure (ring, polyExpr.toPoly)

def toExprPoly (p : CommRing.Poly) : StateT VariableState MetaM (ExprPoly) := do
  let state ← get
  let coeff := Std.TreeMap.ofList <| state.coefficientTable.toList.map Prod.swap
  pure {
    poly := p
    coefficients := coeff
  }

def m2IdealMembership
  [Macaulay2Ring R]
  (I : List CommRing.Poly)
  (f : CommRing.Poly) :
  IO (Option (List CommRing.Poly)) := sorry

def proveIdealMembership : TacticM Unit := do
  sorry

syntax (name := m2idealmem) "m2idealmem" notFollowedBy("|") (ppSpace colGt term:max)* : tactic

unsafe def m2IdealMemTacticImpl (goal : MVarId) (idealExprs : Array Expr) (polyExpr : Expr)
  : TacticM Unit := do
  --parse a expression into a polynomial, checking that the ring matches using isDefEq
  let getPoly (expectedRing : Expr) (pExpr : Expr) : StateT VariableState MetaM ExprPoly := do
    let some (ring, poly) ← eqExprToPoly pExpr | throwTacticEx `m2idealmem goal "Expected a polynomial equality"
    if ← isDefEq expectedRing ring
    then toExprPoly poly
    else throwTacticEx `m2idealmem goal "Expected polynomials over the same base ring"
  let getPolys := do
    let some (ring, poly) ← eqExprToPoly polyExpr | throwTacticEx `m2idealmem goal "Expected a polynomial equality"
    let exprPoly ← toExprPoly poly
    let genPolys ← idealExprs.mapM (getPoly ring)
    pure <| some (ring, genPolys, exprPoly)
  let some (ring, idealGens, poly) ← getPolys.run' .empty | throwTacticEx `m2idealmem goal "Expected a polynomial expression"

  let serializerExpr ← mkAppOptM ``serializePoly #[ring, none]
  let serializerType ← inferType serializerExpr
  let serializer ← evalExpr (ExprPoly → MrdiT TacticM (Option Mrdi)) serializerType serializerExpr DefinitionSafety.unsafe
  let deserializerExpr ← mkAppOptM ``deserializePoly #[ring, none, none]
  let deserializerType ← inferType deserializerExpr
  let deserializer ← evalExpr (Mrdi → MrdiT TacticM (Except String ExprPoly)) deserializerType deserializerExpr DefinitionSafety.unsafe
  let s ← IO.rand 0 (2^64-1)
  --I should be able to use the runMrdiIO variant
  -- but I can't get it to infer the right MonadLift instance
  runMrdiWithSeed s do
    let some serializedPoly ← serializer poly
      | throwTacticEx `m2idealmem goal "Unable to serialize polynomial"
    let serializedGens : Array (Option Mrdi) ← idealGens.mapM serializer
    --check that ring is a ring we know how to work with
    logInfo <| toString <| toJson serializedPoly
    logInfo <| toString <| toJson serializedGens
    let .ok (newExprPoly : ExprPoly) ← deserializer serializedPoly
      | throwTacticEx `m2idealmem goal "Unable to deserialize polynomial"
    -- logInfo <| repr <| newExprPoly

@[tactic m2idealmem]
unsafe def m2IdealMemTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| m2idealmem [$args,*]) =>
    let goal ← getMainGoal
    let target ← getMainTarget
    let gens ← args.getElems.mapM (fun g => do
      match (← elabTerm g none) with
      | .fvar var =>
        let varDec ← var.getDecl
        pure <| varDec.type
      | e => pure <| e)
    m2IdealMemTacticImpl goal gens target
  | _ => throwTacticEx `m2idealmem (← getMainGoal) "Expect list of equalities for the ideal"

example {x y : Rat} (f : 1/2*x + 1/2*y = 0) (g : 1/2*x + 1/2*y = 0) : (x + y)^2 = 0 := by
  m2idealmem [f, g]
  sorry
