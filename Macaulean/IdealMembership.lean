import Lean
import MRDI.Basic
import MRDI.Poly
open Lean Grind Elab Tactic Meta

structure VariableState where
  varTable : FVarIdMap CommRing.Var
  coefficientTable : Std.HashMap Lean.Expr CommRing.Var --equality of expressions is probably wrong
  nextVar : CommRing.Var

#check Grind.Arith.CommRing.State

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
    let .ok ((num, den) : Int × Nat) := fromJson? x | return .error "Expected a pair"
    if den = 0
    then pure <| .error "Expected a non-zero denominator"
    else pure <| .ok <| mkRat num den
  encode (x : Rat) := pure <| .arr #[x.num, x.den]

instance : Macaulay2Ring Int where
  mrdiDesc := pure <| .str "Int" --TODO actually think about this representation
  fromLitExpr? := getIntValue?

instance : Macaulay2Ring Rat where
  mrdiDesc := pure <| .str "Rat"
  fromLitExpr? := getRatValue?

structure ConcretePoly (R : Type) where
  poly : CommRing.Poly
  coefficients : Std.TreeMap CommRing.Var R

unsafe instance [MrdiType R] : MrdiType (ConcretePoly R) where
  --TODO this should really be a parameterized mrdiType, but those require better UUID infrastructure
  mrdiType := .parameterized "ConcretePoly" (.str <| toString <| MrdiType.mrdiType (α := R))
  decode? (x : Json) := pure <| .ok <| {
    poly := .num 0
    coefficients := .empty
  }
  --TODO use UUID's and references to do this properly
  encode (p : ConcretePoly R) := do
    let basePolyUuid ← addReference p.poly
    let coefficients ← p.coefficients.toArray.mapM (fun (i,x) => (i, ·) <$> MrdiType.encode x)
    pure <| Json.mkObj [
      ("poly", toJson basePolyUuid),
      ("coefficients", .arr <| coefficients.map toJson) ]

structure ExprPoly where
  poly : CommRing.Poly
  coefficients : Std.TreeMap Nat Expr

unsafe def serializePoly [Macaulay2Ring R] (p : ExprPoly) : MrdiT MetaM (Option Mrdi) := do
  let convertedCoefficientsOpt : List (Nat × Option R) ←
    p.coefficients.toList.mapM (fun (i,x) => (i, ·) <$> Macaulay2Ring.fromLitExpr? x)
  let some convertedCoefficients := convertedCoefficientsOpt.mapM
    (fun (x,y) => (x, ·) <$> y) | return none
  let concretePoly : ConcretePoly R := {
    poly := p.poly
    coefficients :=  Std.TreeMap.ofList convertedCoefficients }
  some <$> toMrdi concretePoly

--inspired by Grind.Arith.CommRing.reify?
partial def toCommRingExpr?
  (x : Lean.Expr)
  : StateT VariableState MetaM (Option CommRing.Expr) := do
  match_expr x with
  --TODO: figure out what we need to be careful about with types
  | HAdd.hAdd _ _ _ _ a b =>
    pure <| .add <$> (← toCommRingExpr? a) <*> (← toCommRingExpr? b)
  | HMul.hMul _ _ _ _ a b =>
    pure <| .mul <$> (← toCommRingExpr? a) <*> (← toCommRingExpr? b)
  | HSub.hSub _ _ _ _ a b =>
    pure <| .sub <$> (← toCommRingExpr? a) <*> (← toCommRingExpr? b)
  | HPow.hPow _ _ _ _ a b =>
    pure <| .pow <$> (← toCommRingExpr? a) <*> (← getNatValue? b)
  -- | HDiv.hDiv _ _ _ _ a b => pure <| none
  --^ TODO actually implement, should work if b is an element of R and R is a field
  --TODO what to do with free meta variables???
  | _ =>
    match x with
    | .fvar varId =>
      let varName ← modifyGet (
        fun varState => varState.mapVariable varId)
      pure <| some <| .var varName
    | _ =>
      let varName ← modifyGet (
        fun varState => varState.mapCoefficient x)
      pure <| some <| .var varName

def eqExprToPoly
  (expr : Expr)
  : StateT VariableState MetaM (Option (Expr × CommRing.Poly)) := do
  let some (ring,lhs,rhs) := expr.eq? | return none
  IO.println rhs
  let polyExpr : Option (CommRing.Expr) :=
    .sub <$> (← toCommRingExpr? lhs) <*> (some <| .natCast 0) -- (← toCommRingExpr? rhs)
  pure <| (ring, · ) <$> CommRing.Expr.toPoly <$> polyExpr

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
    let some (ring, poly) ← eqExprToPoly (← whnf pExpr) | throwTacticEx `m2idealmem goal "Expected a polynomial equality"
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
  let serializer ← evalExpr (ExprPoly → MrdiT MetaM (Option Mrdi)) serializerType serializerExpr DefinitionSafety.unsafe
  let serializedPoly : Option Mrdi ← (serializer poly).run' .empty
  let serializedGens : Array (Option Mrdi) ← (idealGens.mapM serializer).run' .empty
  --check that ring is a ring we know how to work with
  logInfo <| repr polyExpr
  logInfo <| toString <| toJson serializedPoly
  logInfo <| toString <| toJson serializedGens

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

/-
{
type = {"ConcretePoly", params := (data about which ring it's over)}
data = [x_1*x_2+x_5*x_3+x_4, (1,1/2), (5,3)]
}
represents
1/2*x_2+3*x_3+x_4

Eventual format?
{
  poly := x_1*x_2+x_5*x_3+x_4
  coefficients := [(1,1/2), (5,3)]
}
-/
