import Lean
open Lean Grind Elab Tactic Meta

-- a helper theorem, this is just congr but it makes life easier
theorem congrPlus [Add R] {a b c d : R} (h1 : a = b) (h2 : c = d) : a + c = b + d :=
  by congr

theorem congrSub [Sub R] {a b c d : R} (h1 : a = b) (h2 : c = d) : a - c = b - d :=
  by congr

theorem congrMul [Mul R] {a b c d : R} (h1 : a = b) (h2 : c = d) : a * c = b * d :=
  by congr


--grind is overkill, but it works
theorem mulSwap [CommRing R] (a b c : R) : a * b * c = a * c * b := by grind


inductive FactorType where
  | coeff : FactorType
  | var (v : Nat) : FactorType
  | poly : FactorType
deriving Ord, BEq

instance : LT FactorType := ltOfOrd
instance : LE FactorType := leOfOrd

-- for now this uses the simpler bubble sort strategy, since there tend to be fewer layers of multiplcation
-- returns a pair of a proof of the reordering and the reordered expression
-- expects all of the multiplications to already be associated appropriately
partial def reorderVars (vars : Array FVarId) (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    let (aProof, aReorder) ← reorderVars vars a
    let (bProof, bReorder) ← reorderVars vars b
    pure (← mkAppM ``congrPlus #[aProof, bProof], ← mkAdd aReorder bReorder)
  | HMul.hMul _ _ _ _ d c =>
    let (dProof, dReorder) ← reorderVars vars d
    let (cProof, cReorder) ← reorderVars vars c
    let (lastEquality, lastReorder) ← insertFactorSorted dReorder cReorder
    --combine the proofs
    let firstEquality ← mkAppM ``congrMul #[dProof,cProof]
    pure (← mkAppM ``Eq.trans #[firstEquality,lastEquality], lastReorder)
  | _ => pure (← mkEqRefl e, e)
  where
    factorType (e : Expr) : FactorType :=
    match_expr e with
    | HAdd.hAdd _ _ _ _ _ _ => .poly
    | _ =>
      let maybeIdx := e.fvarId? >>= vars.idxOf?
      (maybeIdx.map .var).getD .coeff
    --assuming that a is a sequence of HMul.hMul applications, insert b into the sequence
    --sorted in the correct way along with a proof that a*b = result
    insertFactorSorted (a b : Expr) : MetaM (Expr × Expr) := do
      --TODO merge equal factors
      --TODO if b is a polynomial, put it at the end
      let bOrder := factorType b
      match_expr a with
      | HMul.hMul _ _ _ _ a1 a2 =>
        let a2Order := factorType a2;
        if a2Order <= bOrder
        then pure (← mkEqRefl (← mkMul a b), ← mkMul a b)
        else
          let (nextStep,nextTerm) ← insertFactorSorted a1 b
          let currStep ← mkAppM ``mulSwap #[a1,a2,b]
          let liftedNextStep ←
            mkAppM ``congrMul #[nextStep, ← mkEqRefl a2] --this is a bit of a silly way of doing this
          pure (← mkAppM ``Eq.trans #[currStep, liftedNextStep], ← mkMul nextTerm a2)
      | _ =>
        let aOrder := factorType a
        if aOrder <= bOrder
        then pure (← mkEqRefl (← mkMul a b), ← mkMul a b)
        else pure (← mkAppM ``CommRing.mul_comm #[a, b], ← mkMul b a)

syntax (name := reorder) "reorder" notFollowedBy("|") (ppSpace colGt term:max)*  : tactic

@[tactic reorder]
unsafe def reorderTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| reorder [$args,*] ) =>
    let goal ← getMainGoal
    let target ← getMainTarget
    let varExprs ← args.getElems.mapM (elabTerm · none)
    let vars := varExprs.map Expr.fvarId!
    let .some (_,lhs,rhs) := target.eq? | throwTacticEx `reorder goal "Expected an equality"
    let (eqProof,expectedTarget) ← reorderVars vars rhs
    let eqGoalMVar ← mkFreshExprMVar (← mkEq lhs expectedTarget)
    goal.assign (← mkEqTrans eqGoalMVar (← mkEqSymm eqProof))
    pushGoal eqGoalMVar.mvarId!
  | _ => throwTacticEx `reorder (← getMainGoal) "Invalid Syntax"

example (a b c : Rat) : a*b*c = c*b*a := by
  reorder [a,b,c]
  trivial

example (a b c : Rat) : 2*a*b*c+3*a*b = c*2*b*a+b*a*3 := by
  reorder [a,b,c]
  trivial

/--
  reorder terms into grevlex order using the variables in vars.
  returns a proof of equality.
  will reorder things that don't look like terms based on the lead term.
  i.e. x*(y+z)+x gets reordered treating the first term as if it was x*y
  treats variables and other expressions not showing up in vars as constants (pushes them to the back)
-/
partial def reorderTerms (vars : List FVarId) (e : Expr) (ring : Expr) : MetaM Expr := do
  let (_,res) ← reorderAndLeadTerm e
  pure res
  where
    --the returned expr is a proof of equality
    --problem: we can only really do a bubble sort, which isn't great for efficiency,
    --maybe do a merge sort? but we have to prove the associativity step....
    reorderAndLeadTerm (e : Expr) : MetaM (Grind.CommRing.Mon × Expr) := do
      match_expr e with
      | HAdd.hAdd _ _ _ _ a b =>
        let (aMon,aReorder) ← reorderAndLeadTerm a
        let (bMon,bReorder) ← reorderAndLeadTerm b
        let termMon := aMon.mul bMon
        match aMon.grevlex bMon with
        | .gt => pure (termMon, sorry)
        | _ => pure (termMon, sorry)
      | HMul.hMul _ _ _ _ a b =>
      --TODO we really should factor out the constant terms
        let (aMon,aReorder) ← reorderAndLeadTerm a
        let (bMon,bReorder) ← reorderAndLeadTerm b
        pure (aMon.mul bMon, sorry)
      | _ => sorry
    exprLeadMonomial (e : Expr) : MetaM Grind.CommRing.Mon := sorry
    -- split a sum in half, give a proof of equality and return the two halves as expressions
    -- the returned values will expressions representing the following (originalExpr = a + b, a, b)
    halfAssociate (e : Expr) : MetaM (Expr × Expr × Option Expr) := do
      let subSums := toSubSums e
      let halfLength := subSums.length / 2
      if halfLength == 0
      then pure (← mkEqRefl e, e, none)
      else
        -- leadSum is the first half of the sum
        -- tailSums are all of the partial sums for the rest of the expression
        let (firstTailSum :: remainingTailSums, leadSum :: _) :=
          subSums.splitAt halfLength | throwError "Impossible"
        let_expr HAdd.hAdd _ _ _ _ _ firstTailTerm := firstTailSum
          | throwError "Impossible"
        let (assocProof, tailSumExpr) ← remainingTailSums.foldrM (fun currSum (currProof,currTail) => do
          let_expr HAdd.hAdd _ _ _ _ a b := currSum | throwError "Impossible"
          pure (← mkAppM ``Semiring.add_assoc #[leadSum , currTail,b], ← mkAdd currTail b)) (← mkEqRefl firstTailSum, firstTailTerm)
        pure (assocProof, leadSum, .some tailSumExpr)
    --at every step also keep the expression passed in
    --note that the standard notation for addition associates in the opposite direction to lists
    toSubSums (e : Expr) : List Expr :=
    match_expr e with
      | HAdd.hAdd _ _ _ _ a b => e :: toSubSums a
      | _ => [e]
