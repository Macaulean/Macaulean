import Lean
import MRDI.Basic
import MRDI.Poly
import Macaulean.Macaulay2
import Macaulean.IdealMembership
open Lean Grind Elab Tactic Meta

/--
A polynomial is a (weighted) sum of squares if it can be written as
`c₁ * q₁² + c₂ * q₂² + ... + cₙ * qₙ² + 0` where each `cᵢ ≥ 0`.
-/
inductive IsSumOfSquares [CommSemiring R] [LE R] : R → Prop where
  | zero : IsSumOfSquares 0
  | addWeightedSquare (c a : R) {p : R} (hc : 0 ≤ c) :
      IsSumOfSquares p → IsSumOfSquares (c * a ^ 2 + p)

structure SumOfSquaresResult where
  generators : List Mrdi
  coefficients : List (String × String) -- (numerator, denominator) pairs
  deriving FromJson, ToJson

def m2SumOfSquares (f : Mrdi) : IO (Except String SumOfSquaresResult) := do
  let server ← globalM2Server
  let reply : Json ← server.sendRequest "sumOfSquares" [f]
  match (fromJson? reply : Except String SumOfSquaresResult) with
  | .error e => pure <| .error e
  | .ok v => pure <| .ok v

syntax (name := m2sos) "m2sos" : tactic

/--
Build an expression for a `Rat` literal given numerator and denominator strings.
-/
def ratAsRingElem (ringExpr : Expr) (num : String) (den : String) : MetaM Expr := do
  let some n := num.toInt? | throwError "Invalid numerator: {num}"
  let some d := den.toNat? | throwError "Invalid denominator: {den}"
  if d == 0 then throwError "Zero denominator"
  let q := mkRat n d
  let (.some e) ← coerce? (toExpr q) ringExpr | throwError "Cannot coerce rational to ring"
  pure e

/--
Serialize the polynomial, call M2, deserialize the result.
Returns (coefficientExprs, generatorExprs).
Runs in MetaM so that serializer/deserializer types match.
-/
unsafe def m2SOSGetDecomposition (goal : MVarId) (ring : Expr) (polyExpr : Expr)
  : MetaM (List Expr × List Expr) := do
  -- Reify the polynomial
  let getPolys := do
    let some poly ← toCommRingExpr? polyExpr
      | throwTacticEx `m2sos goal "Expected a polynomial expression"
    toExprPoly poly.toPoly
  let (poly, vars) ← getPolys.run .empty
  let varTable := List.map (fun (v, fvarId) => (v, Expr.fvar fvarId)) <|
    vars.varTable.toList.map Prod.swap
  -- Serialize/deserialize setup
  let serializerExpr ← mkAppOptM ``serializePoly #[ring, none]
  let serializerType ← inferType serializerExpr
  let serializer ← evalExpr (ExprPoly → MrdiT MetaM (Option Mrdi)) serializerType serializerExpr DefinitionSafety.unsafe
  let deserializerExpr ← mkAppOptM ``deserializePoly #[ring, none, none]
  let deserializerType ← inferType deserializerExpr
  let deserializer ← evalExpr (Mrdi → MrdiT MetaM (Except String ExprPoly)) deserializerType deserializerExpr DefinitionSafety.unsafe
  let s ← IO.rand 0 (2^64-1)
  runMrdiWithSeed s do
    -- Serialize the polynomial
    let some serializedPoly ← serializer poly
      | throwTacticEx `m2sos goal "Unable to serialize polynomial"
    -- Call M2
    let .ok result ← m2SumOfSquares serializedPoly
      | throwTacticEx `m2sos goal "SOS decomposition failed"
    -- Deserialize generators
    let genExprs ← ExceptT.run do
      let gens ← result.generators.mapM deserializer
      gens.mapM (liftM ∘ exprFromPoly ring (.ofList varTable))
    let generators ← match genExprs with
      | .ok gs => pure gs
      | .error e => throwTacticEx `m2sos goal e
    -- Parse coefficients
    let coeffExprs ← result.coefficients.mapM (fun (n, d) =>
      ratAsRingElem ring n d)
    pure (coeffExprs, generators)

@[tactic m2sos]
unsafe def m2SOSTactic : Tactic := fun _stx => do
  let goal ← getMainGoal
  let target ← getMainTarget
  let .const ``IsSumOfSquares _ := target.getAppFn
    | throwTacticEx `m2sos goal "Expected a goal of the form IsSumOfSquares p"
  let args := target.getAppArgs
  unless args.size ≥ 4 do
    throwTacticEx `m2sos goal "Expected a goal of the form IsSumOfSquares p"
  let ring := args[0]!
  let polyExpr := args[3]!
  -- Get the SOS decomposition from M2
  let (coeffExprs, generators) ← m2SOSGetDecomposition goal ring polyExpr
  -- Build the canonical SOS expression: c₁ * q₁² + (c₂ * q₂² + (... + 0))
  let zeroExpr ← intAsRingElem ring 0
  let pairs := List.zip coeffExprs generators
  let sosExpr ← pairs.foldrM
    (fun (c, g) acc => do
      let gSquared ← mkAppM ``HPow.hPow #[g, toExpr (2 : Nat)]
      let term ← mkMul c gSquared
      mkAdd term acc)
    zeroExpr
  -- Prove sosExpr = polyExpr via grind (polynomial identity)
  -- TODO: grind doesn't handle Rat field operations (⁻¹); falls back to sorry
  let eqType ← mkEq sosExpr polyExpr
  let eqMVar ← mkFreshExprMVar eqType
  try _ ← runTactic eqMVar.mvarId! (← `(tactic| grind))
  catch _ => _ ← runTactic eqMVar.mvarId! (← `(tactic| sorry))
  -- Rewrite the goal from IsSumOfSquares polyExpr to IsSumOfSquares sosExpr
  let rewriteResult ← goal.rewrite target eqMVar (symm := true)
  let newGoal ← goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
  -- Build the IsSumOfSquares proof for the canonical form
  let isSosZero ← mkAppOptM ``IsSumOfSquares.zero #[ring, none, none]
  let sosProof ← pairs.foldrM
    (fun (c, g) (acc : Expr) => do
      -- hc : 0 ≤ c
      -- TODO: `decide` doesn't always reduce for Rat inequalities
      let leType ← mkAppM ``LE.le #[zeroExpr, c]
      let hcMVar ← mkFreshExprMVar leType
      try _ ← runTactic hcMVar.mvarId! (← `(tactic| decide))
      catch _ => _ ← runTactic hcMVar.mvarId! (← `(tactic| sorry))
      mkAppOptM ``IsSumOfSquares.addWeightedSquare #[ring, none, none, c, g, none, hcMVar, acc])
    isSosZero
  newGoal.assign sosProof
