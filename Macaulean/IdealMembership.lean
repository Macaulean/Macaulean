import Lean
import MRDI.Basic
import MRDI.Poly
import Macaulean.Macaulay2
import Macaulean.Polynomial
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
-- Integers travel as decimal *strings*, the same convention `Rat`,
-- `Grind.CommRing.Power` and `MRDI.Term` already use.  A bare JSON number is
-- not loadable on the Macaulay2 side: `MRDI.m2`'s `fromMRDI` recursion has
-- methods for hash tables, strings and lists only, so a number anywhere inside
-- `data` aborts the request.
instance : MrdiType Int where
  mrdiType := .string "Int"
  decode? (x : Json) := pure <|
    match x with
    | .str s => (s.toInt?).elim (.error s!"Expected a String representing an Int {s}") .ok
    | j => fromJson? j
  encode (x : Int) := pure <| .str (toString x)

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

def natAsRingElem (ringExpr : Expr) (k : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[ringExpr, mkRawNatLit k, none]

def intAsRingElem (ringExpr : Expr) (k : Int) : MetaM Expr := do
  let a := k.natAbs
  let aExpr ← natAsRingElem ringExpr a
  if k >= 0
  then pure aExpr
  else mkAppM ``Neg.neg #[aExpr]

/--
Reify `x`, an expression of the *ambient* ring, as a `Macaulean.Polynomial ring
nv` -- where `ring` is the ring the coefficients travel in, which need not be
the ambient one (see `m2QuotientRemainderRaw`'s `coeffRing`).

What counts as a ring operation, a coefficient or a **variable** is
`Macaulean.AlgPoly.Reify.classify`'s decision, not this function's: any maximal
non-arithmetic subterm is a variable, identified with the ones already seen up
to definitional equality, and numbered by first occurrence.  A free variable is
the special case where that subterm happens to be an `fvar`; `MvPolynomial.X 0`
and `f x y` are variables on exactly the same footing, which is what lets a
goal over `MvPolynomial (Fin 3) ℚ` make the round trip at all.

Sharing the classifier with the reflective half is the point: Macaulay2's
cofactors come back as exponent vectors over *these* variables, in *this*
numbering, and `poly_cert` has to rebuild them as terms the kernel then reifies
the same way.

Numerals and unary minus are translated rather than treated as opaque
constants, which is what lets the two rings differ: a goal over
`MvPolynomial (Fin 3) ℚ` whose `CASRing` instance says `QQ` sends its
coefficients as `Rat`.  When the two rings *are* the same -- every caller
before `m2cert` -- the numeral branch rebuilds the numeral it was given, so
nothing changes.
-/
partial def toPolynomialExpr (nv : Nat) (ring : Expr) (x : Lean.Expr) :
    Macaulean.AlgPoly.Reify.AtomM Lean.Expr := do
  match ← liftM (Macaulean.AlgPoly.Reify.classify x) with
  | .add a b => mkAdd (← toPolynomialExpr nv ring a) (← toPolynomialExpr nv ring b)
  | .sub a b => mkSub (← toPolynomialExpr nv ring a) (← toPolynomialExpr nv ring b)
  | .mul a b => mkMul (← toPolynomialExpr nv ring a) (← toPolynomialExpr nv ring b)
  | .neg a => mkAppM ``Neg.neg #[← toPolynomialExpr nv ring a]
  | .pow a k => mkAppM ``HPow.hPow #[← toPolynomialExpr nv ring a, mkNatLit k]
  | .coeff k =>
    mkAppOptM ``Macaulean.Polynomial.ofConst #[ring, toExpr nv, ← intAsRingElem ring k]
  | .atom =>
    let i ← Macaulean.AlgPoly.Reify.mkAtom x
    mkAppOptM ``Macaulean.Polynomial.ofVar #[
      ring, none, none, ← mkAppOptM ``Fin.ofNat #[toExpr nv, none, toExpr i]]

def toExprPoly (p : CommRing.Poly) : StateT VariableState MetaM (ExprPoly) := do
  let state ← get
  let coeff := Std.TreeMap.ofList <| state.coefficientTable.toList.map Prod.swap
  pure {
    poly := p
    coefficients := coeff
  }

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
  deriving Inhabited, Repr

declare_config_elab configElab Config

end Macaulean.IdealMembership

open Macaulean

unsafe def serializePoly [Macaulay2Ring R] (p : Macaulean.Polynomial R n)
  : MrdiT MetaM (Option Mrdi) := do
  .some <$> toMrdi p

unsafe def deserializePoly (n : Nat) [ToExpr R] [Macaulay2Ring R] (polyMrdi : Mrdi)
  : MrdiT MetaM (Except String Lean.Expr) := ExceptT.run do
  let poly : Polynomial R n ← fromMrdi? polyMrdi
  pure <| toExpr poly

abbrev SeralizationPair := (Expr → MrdiT MetaM (Option Mrdi)) × (Mrdi → MrdiT MetaM (Except String Lean.Expr))

unsafe def makePolynomialSerializationPair (ring : Expr) (n : Nat) : MetaM SeralizationPair := do
  let doDeserializationExpr ← liftM <| mkAppOptM ``deserializePoly #[ring, toExpr n, none, none]
  let deserializationExprType ← liftM <| inferType doDeserializationExpr
  let doDeserialization ← liftM <|
    evalExpr (Mrdi → MrdiT MetaM (Except String Lean.Expr)) deserializationExprType doDeserializationExpr DefinitionSafety.unsafe
  pure (
    fun e => do
      let doSerializationExpr ← liftM <| mkAppOptM ``serializePoly #[ring, none, none, e]
      let exprType ← liftM <| inferType doSerializationExpr
      let doSerialization ← liftM <| evalExpr (MrdiT MetaM (Option Mrdi)) exprType doSerializationExpr DefinitionSafety.unsafe
      doSerialization
    ,
    doDeserialization
  )

/--
Reify `polyExpr` and `idealExprs` as `Macaulean.Polynomial`s over `ring`, ask
Macaulay2 to divide the first by the rest, and hand back the reply *as it
arrived* along with the **atoms** it was written in, in the index order both
the request and the reply use.

An atom is any maximal non-arithmetic subterm (see
`Macaulean.AlgPoly.Reify.classify`), so `x`, `MvPolynomial.X 0` and `f x y` are
all variables of the request; Macaulay2 sees them as its own `a, b, c, …` at
the matching positions.  They are numbered by first occurrence, left to right,
starting from `polyExpr` and then running through `idealExprs`, which makes the
numbering -- and so `m2cert?`'s printed `in [...]` clause -- reproducible.

`m2QuotientRemainderImpl` deserializes that reply into `Polynomial.denote`
expressions; `m2cert` (`Macaulean/M2Cert.lean`) reads the monomials out of it
directly, to build the certificate in the ambient ring instead.

`coeffRing` is the ring the coefficients are serialised in -- the Macaulay2
base ring.  It defaults to the ambient ring, which is what every caller wanted
back when the ambient ring was always `Int` or `Rat`; `m2cert` passes what the
ambient ring's `Macaulean.CASRing` instance asks for.
-/
unsafe def m2QuotientRemainderRaw (goal : MVarId) (ring : Expr) (idealExprs : Array Expr)
  (polyExpr : Expr) (coeffRing : Option Expr := none) :
  MetaM (Array Expr × QuotientRemainder) := do
  dbg_trace "M2IdealMem Start"

  --TODO reimplement universalization in a more systematic way

  -- One pass for the atoms, because `Polynomial R nv` names `nv` in its type
  -- and so the builder needs it up front; a second to build.  The second pass
  -- re-runs the same classification over the same terms, so it discovers no
  -- atom the first did not -- which is checked rather than assumed.
  let atomState0 ← Macaulean.AlgPoly.Reify.atomStateOf (#[polyExpr] ++ idealExprs)
  let nv := atomState0.atoms.size
  if nv == 0 then
    throwTacticEx `m2idealmem goal
      "the goal has no ring variables, so there is nothing for Macaulay2 to work with"
  -- The Macaulay2 base ring.  `none` keeps the historical behaviour -- the
  -- coefficients travel in the ambient ring itself, which is why this used to
  -- work only for ambient rings that happen to carry a `Macaulay2Ring`
  -- instance.  `m2cert` passes the ring its `Macaulean.CASRing` instance
  -- names (`Int` for `ZZ`, `Rat` for `QQ`) instead.
  let cring := coeffRing.getD ring
  let ((polyExprPoly, idealExprsPolys), atomState) ← (do
      let p ← toPolynomialExpr nv cring polyExpr
      let gs ← idealExprs.mapM (toPolynomialExpr nv cring)
      pure (p, gs)).run atomState0
  unless atomState.atoms.size == nv do
    throwTacticEx `m2idealmem goal
      "the atom pass and the building pass disagreed on the variables"
  let atoms := atomState.atoms

  let (serializer,_) ← makePolynomialSerializationPair cring nv

  let s ← IO.rand 0 (2^64-1)
  --I should be able to use the runMrdiIO variant
  -- but I can't get it to infer the right MonadLift instance
  runMrdiWithSeed s do
    --serialize the polynomials
    let some serializedPoly ← serializer polyExprPoly
      | throwTacticEx `m2idealmem goal "Unable to serialize polynomial"
    let serializedGens : Array (Option Mrdi) ← (idealExprsPolys.mapM serializer)
    let some serializedGens := serializedGens.mapM id
      | throwTacticEx `m2idealmem goal "Unable to serialize ideal generators"
    --run Macaulay2
    dbg_trace "Calling Macaulay2"
    let .ok result ← m2QuotientRemainder serializedGens.toList serializedPoly
      | throwTacticEx `m2idealmem goal "Ideal membership failed"
    dbg_trace "Coefficients Returned"
    pure (atoms, result)

/--
This function implements the core of the tactic, serializing and deserializing
the polynomials to Macaulay2. `ring` should be an expression for the ring
`idealExprs` should be a list of generators for the ideal and `polyExpr` should be
the candidate polynomial. The returned list of expressions is a list of
coefficients such that the product with the generators in idealExprs gives polyExpr
-/
unsafe def m2QuotientRemainderImpl (goal : MVarId) (ring : Expr) (idealExprs : Array Expr) (polyExpr : Expr)
  : MetaM (List Expr × Expr) := do
  let (atoms, result) ← m2QuotientRemainderRaw goal ring idealExprs polyExpr
  let varContextExpr ← mkAppM ``RArray.ofArray
    #[← mkArrayLit ring atoms.toList,
      ← mkAppM ``Nat.succ_pos #[toExpr (atoms.size - 1)]]
  let (_,deserializer) ← makePolynomialSerializationPair ring atoms.size
  let s ← IO.rand 0 (2^64-1)
  runMrdiWithSeed s do
    --deserialize the result
    let deserializedCoefficients ← ExceptT.run do
      result.quotient.mapM deserializer
    let deserializedRemainder ← ExceptT.run do
      deserializer result.remainder
    match deserializedCoefficients, deserializedRemainder with
    | .ok c, .ok r  => pure (
      ← c.mapM fun x =>
          mkAppM ``Macaulean.Polynomial.denote #[varContextExpr, x],
      ← mkAppM ``Macaulean.Polynomial.denote #[varContextExpr, r])
    | .error e, _ => throwTacticEx `m2idealmem goal e
    | _, .error e => throwTacticEx `m2idealmem goal e

--TODO rename this
theorem helper [CommRing R] (a b c d : R) (h1 : a = d) (h2 : b = 0) : a+c*b = d := by
  rewrite [h1,h2]
  simp [Semiring.mul_zero,Semiring.add_zero]

--this theorem really should be proven elsewhere
private theorem RArray_get_ofArray (h : i < arr.size) : (RArray.ofArray arr len_hyp).get i = arr[i] := by
  have irw : i = ↑(Fin.mk i h) := by simp
  conv =>
    left
    right
    rw [irw]
  rw [RArray.ofArray, RArray.get_ofFn]
  simp

--as should this one
private theorem Semiring_zero_add [Semiring R] (a : R) : 0 + a = a := by grind

set_option stderrAsMessages false

-- factor out the core tactic to make the code a bit simpler
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
    let (newGoals,_) ←
      runTactic (← getMainGoal) (← `(tactic|simp (maxSteps:=100000) [Macaulean.Polynomial.denote, Macaulean.Mon.denote, Macaulean.Mon.mon_powers_simproc, RArray_get_ofArray, Semiring_zero_add, Semiring.add_zero]))
    setGoals newGoals
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
  let (coeffs,remainder) ← m2QuotientRemainderImpl goal targetRing genPolys targetLhs
  dbg_trace "Coefficients Read"
  let startingExpr ← mkEqRefl targetRhs
  let remainderProof ← (coeffs.zip genHyps.toList).foldlM
    (fun mvar (c,f) => do
      mkAppOptM ``helper #[targetRing, none, none, none, c, none, mvar, f])
    startingExpr
  let remainderProofType ← inferType remainderProof
  let some (_,expectedTarget,_) := remainderProofType.eq?
    | tacticError "Impossible"
  let eqGoalMVar ← mkFreshExprMVar (← mkEq targetLhs (← mkAdd expectedTarget remainder))
  let remainderZeroGoal ← mkFreshExprMVar (← mkEq remainder zeroExpr)
  if ← goal.checkedAssign (← mkEqTrans eqGoalMVar remainderProof)
  then
    dbg_trace "New Goal Created"
    pushGoals [eqGoalMVar.mvarId!]
    let (newGoals,_) ←
      runTactic (← getMainGoal) (← `(tactic|simp [Macaulean.Polynomial.denote, Macaulean.Mon.denote, Macaulean.Mon.mon_powers_simproc, RArray_get_ofArray, Semiring_zero_add, Semiring.add_zero]))
    setGoals newGoals
    pushGoals [remainderZeroGoal.mvarId!]
    let (newGoals2,_) ←
      runTactic (← getMainGoal) (← `(tactic|simp [Macaulean.Polynomial.denote, Macaulean.Mon.denote, Macaulean.Mon.mon_powers_simproc, RArray_get_ofArray, Semiring_zero_add, Semiring.add_zero]))
    pushGoals newGoals2
  else
    tacticError "Failed to show remainder"
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
