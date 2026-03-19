import Lean
open Lean Grind Elab Tactic Meta

--TODO: consider making this either use or be compatible with the conv tactic

-- a helper theorem, this is just congr but it makes life easier
theorem congrPlus [Add R] {a b c d : R} (h1 : a = b) (h2 : c = d) : a + c = b + d :=
  by congr

theorem congrSub [Sub R] {a b c d : R} (h1 : a = b) (h2 : c = d) : a - c = b - d :=
  by congr

theorem congrMul [Mul R] {a b c d : R} (h1 : a = b) (h2 : c = d) : a * c = b * d :=
  by congr

theorem congrPow [HPow R Nat R] {a b : R} (n : Nat) (h1 : a = b) : a ^ n = b ^ n :=
  by congr

--grind is overkill, but it works
theorem mulSwap [CommRing R] (a b c : R) : a * b * c = a * c * b := by grind
theorem plusSwap [Semiring R] (a b c : R) : a + b + c = a + c + b := by grind

theorem semiring_pow_mul [Semiring R] (a : R) (b c : Nat) : (a^b)^c = a^(b*c) := by
  induction c with
  | zero => grind
  | succ n h =>
    rw [Semiring.pow_succ,h,← Semiring.pow_add,Nat.left_distrib,Nat.mul_one]

inductive FactorType where
  | coeff : FactorType
  | var (v : Nat) : FactorType
  | poly : FactorType
deriving Ord, BEq, Inhabited

def FactorType.isVariable : FactorType → Bool
  | .var _ => true
  | _ => false

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
  | HMul.hMul _ _ _ _ c d =>
    let (cProof, cReorder) ← reorderVars vars c
    let (dProof, dReorder) ← reorderVars vars d
    let (lastEquality, lastReorder) ← insertFactorSorted cReorder dReorder
    check lastEquality
    --combine the proofs
    let firstEquality ← mkAppM ``congrMul #[cProof,dProof]
    pure (← mkAppM ``Eq.trans #[firstEquality,lastEquality], lastReorder)
  | HPow.hPow _ _ _ _ a b =>
    --TODO consider simplifying the exponents to nat literals
    let (aProof, aReorder) ← reorderVars vars a
    let liftedProof ← mkAppM ``congrPow #[b,aProof]
    match_expr aReorder with
    | HPow.hPow _ _ _ _ aVar aExp =>
      let powMulStep ← mkAppM ``semiring_pow_mul #[aVar, aExp, b]
      pure (← mkEqTrans liftedProof powMulStep, ← mkAppM ``HPow.hPow #[aVar, ← mkMul aExp b])
    | _ =>
      pure (liftedProof, ← mkAppM ``HPow.hPow #[aReorder,b])
  | _ => pure (← mkEqRefl e, e)
  where
    factorType (e : Expr) : FactorType :=
    match_expr e with
    | HAdd.hAdd _ _ _ _ _ _ => .poly
    | HPow.hPow _ _ _ _ a _ => factorType a
    | _ =>
      let maybeIdx := e.fvarId? >>= vars.idxOf?
      (maybeIdx.map .var).getD .coeff
    /--
      a and b should be powers of the same variable
    -/
    mergePowers (a b : Expr) : MetaM (Expr × Expr) := do
      match_expr a with
      | HPow.hPow _ _ _ _ aBase aExp =>
        match_expr b with
        | HPow.hPow _ _ _ _ bBase bExp =>
          pure (
            ← mkAppM ``Semiring.pow_add #[aBase, aExp, bExp] >>= mkEqSymm,
            ← mkAppM ``HPow.hPow #[aBase, ← mkAppM ``Nat.add #[aExp, bExp]]
          )
        | _ =>
          pure (
            ← mkAppM ``Semiring.pow_succ #[aBase,aExp] >>= mkEqSymm,
            ← mkAppM ``HPow.hPow #[aBase, ← mkAppM ``Nat.succ #[aExp]]
          )
      | _ =>
        match_expr b with
        | HPow.hPow _ _ _ _ _ _ =>
          --rewrite a as a power and reduce to the previous cases
          let aAsPow ← mkAppM ``HPow.hPow #[a, toExpr 1]
          let powProof ← mkAppM ``Semiring.pow_one #[a] >>= mkEqSymm
          let (mergeProof, mergedExpr) ← mergePowers aAsPow b
          pure (← mkEqTrans powProof mergeProof, mergedExpr)
        | _ =>
          pure
            (← mkAppM ``Semiring.pow_two #[a] >>= mkEqSymm,
             ← mkAppM ``HPow.hPow #[a, toExpr 2])
    --assuming that a is a sequence of HMul.hMul applications, insert b into the sequence
    --sorted in the correct way along with a proof that a*b = result
    insertFactorSorted (a b : Expr) : MetaM (Expr × Expr) := do
      let bOrder := factorType b
      match_expr a with
      | HMul.hMul _ _ _ _ a1 a2 =>
        let a2Order := factorType a2;
        if bOrder.isVariable && a2Order == bOrder
        then
          let associateStep ← mkAppM ``Semiring.mul_assoc #[a1, a2, b]
          let (mergeProof, mergedExpr) ← mergePowers a2 b
          pure (
            ← mkEqTrans associateStep mergeProof,
            ← mkMul a1 mergedExpr
            )

        else if a2Order <= bOrder
        then pure (← mkEqRefl (← mkMul a b), ← mkMul a b)
        else
          let (nextStep,nextTerm) ← insertFactorSorted a1 b
          let currStep ← mkAppM ``mulSwap #[a1,a2,b]
          let liftedNextStep ←
            mkAppM ``congrMul #[nextStep, ← mkEqRefl a2] --this is a bit of a silly way of doing this
          pure (← mkAppM ``Eq.trans #[currStep, liftedNextStep], ← mkMul nextTerm a2)
      | _ =>
        let aOrder := factorType a
        if bOrder.isVariable && aOrder == bOrder
        then mergePowers a b
        else if aOrder <= bOrder
        then pure (← mkEqRefl (← mkMul a b), ← mkMul a b)
        else pure (← mkAppM ``CommRing.mul_comm #[a, b], ← mkMul b a)

/--
  reorder terms into grevlex order using the variables in vars.
  returns a proof of equality.
  will reorder things that don't look like terms based on the lead term.
  i.e. x*(y+z)+x gets reordered treating the first term as if it was x*y
  treats variables and other expressions not showing up in vars as constants (pushes them to the back)
-/
partial def reorderTerms (vars : Array FVarId) (e : Expr) (ring : Expr) : MetaM (Expr × Expr) := do
  let (proof, target, _) ← sortTerms e
  check proof
  pure (proof, target)
  where
    --TODO tail recursion
    powMon (m : CommRing.Mon) (n : Nat) : CommRing.Mon :=
      match m with
      | .unit => .unit
      | .mult ⟨v,k⟩ m' => .mult ⟨v,n*k⟩ <| powMon m' n
    termNormalize (e : Expr) : MetaM (Expr × Expr × CommRing.Mon) := do
      match_expr e with
      | HMul.hMul _ _ _ _ a b =>
        let (normAProof, normA, monA) ← termNormalize a
        let (normBProof, normB, monB) ← termNormalize b
        let pf ← mkAppM ``congrMul #[normAProof, normBProof]
        pure (pf, ← mkMul normA normB, monA.mul monB)
      | HAdd.hAdd _ _ _ _ _ _ =>
        let (sortProof, sortedE, mons) ← sortTerms e
        pure (sortProof, sortedE, List.getLast! mons)
      | HPow.hPow _ _ _ _ a b =>
        match ← getNatValue? b with
        | .some bNat =>
          let (normAProof, normA, monA) ← termNormalize a
          let liftedNormAProof ← mkAppM ``congrPow #[b, normAProof]
          pure (liftedNormAProof, ← mkAppM ``HPow.hPow #[normA, b], powMon monA bNat)
        | .none => pure (← mkEqRefl e, e, .unit)
      | _ =>
        match e with
        | .fvar v =>
          let mon := match vars.idxOf? v with
            | .some i => .ofVar i
            | .none => .unit
          pure (← mkEqRefl e, e, mon)
        | _ => pure (← mkEqRefl e, e, .unit)
    -- mons must be in the reverse order of e
    sortTerms (e : Expr) : MetaM (Expr × Expr × List CommRing.Mon) := do
      match_expr e with
      | HAdd.hAdd _ _ _ _ _ _ =>
        let (assocProof, a , .some b) ← halfAssociate e | throwError "Impossible"
        let (sortedAProof,sortedA,monsA) ← sortTerms a
        let (sortedBProof,sortedB,monsB) ← sortTerms b
        let (mergeProof, merged, mergedMons) ← mergeTerms sortedA sortedB monsA monsB
        let sortingProofs ← mkAppM ``congrPlus #[sortedAProof,sortedBProof]
        let fullProof ← mkEqTrans assocProof <| ← mkEqTrans sortingProofs mergeProof
        check fullProof
        checkWithKernel fullProof
        pure (fullProof, merged, mergedMons)
      | _ =>
        let (normalizeProof, normalizeTerm, leadMon) ← termNormalize e
        pure (normalizeProof, normalizeTerm, [leadMon])

    /--
      Take two expressions, e1 e2, with lead terms of the terms in each given by m1 and m2
      rewrite e1+e2 in order given by m1 and m2
      m1 and m2 should be given in REVERSE order i.e. last term of e1 is the first monomial of m1
    -/
    mergeTerms (e1 e2 :Expr) (ms1 ms2 : List Grind.CommRing.Mon) : MetaM (Expr × Expr × List Grind.CommRing.Mon) := do
      match ms1, ms2 with
      | [], _ => pure (← mkEqRefl e2, e2, ms2)
      | _, [] => pure (← mkEqRefl e1, e1, ms1)
      | m1 :: ms1', m2 :: ms2' =>
          --TODO deal with subtraction
          if m1.grevlex m2 == .lt
          then
            if ms1' == []
            then
              /-
                e1 + e2 = e2 + e1
              -/
              pure (← mkAppM ``Semiring.add_comm #[e1,e2], ← mkAdd e2 e1, m1 :: ms2)
            else
              let_expr HAdd.hAdd _ _ _ _ e1' t1 := e1 | throwError "Invalid input to mergeTerms\n {e1}\n {repr ms1}"
              /-
                (e1' + t1) + e2 = (e1' + e2) + t1)
                = (mergeTerms e1' e2) + t1
              -/
              let swapProof ← mkAppM ``plusSwap #[e1', t1, e2]
              let (leadPartProof, leadPart, newMons) ← mergeTerms e1' e2 ms1' ms2
              let liftedLeadPartProof ← mkAppM ``congrPlus #[leadPartProof, ← mkEqRefl t1]
              let finalExpr ← mkAdd leadPart t1
              pure (← mkEqTrans swapProof liftedLeadPartProof, finalExpr, m1 :: newMons)
          else
            if ms2' == []
            then
              /-
                e1 + e2 = e1 + e2
              -/
              let expr ← mkAdd e1 e2
              pure (← mkEqRefl expr, expr, m2 :: ms1)
            else
              let_expr HAdd.hAdd _ _ _ _ e2' t2 := e2 | throwError "Invalid input to mergeTerms\n {e2}\n {repr ms2}"
              /-
                (e1' + t1) + (e2' + t2) = ((e1' + t1) + e2') + t2)
                = (mergeTerms (e1' + t1) e2') + t1
              -/
              let swapProof ← mkEqSymm (← mkAppM ``Semiring.add_assoc #[e1, e2', t2])
              let (leadPartProof, leadPart, newMons) ← mergeTerms e1 e2' ms1 ms2'
              let liftedLeadPartProof ← mkAppM ``congrPlus #[leadPartProof, ← mkEqRefl t2]
              let finalExpr ← mkAdd leadPart t2
              pure (← mkEqTrans swapProof liftedLeadPartProof, finalExpr, m2 :: newMons)

    --not currently tail recursive because that's hard to get right
    split (n : Nat) (e : Expr) : MetaM (Expr × Expr × Option Expr) := do
      if n == 0
      then pure (← mkEqRefl e, e, .none)
      else
        let_expr HAdd.hAdd _ _ _ _ a b := e | throwError "Invalid split"
        let (prevProof, head, prevTailOpt) ← split (n-1) a
        match prevTailOpt with
        | some prevTail =>
          let tail ← mkAdd prevTail b
          -- turns a = head + prevTail into a + b = (head + prevTail) + b
          let liftedProof ← mkAppM ``congrPlus #[prevProof, ← mkEqRefl b]
          -- (head + prevTail) + b = head + (prevTail + b)
          let commStep ← mkAppM ``Semiring.add_assoc #[head, prevTail, b]
          pure (← mkEqTrans liftedProof commStep, head, .some tail)
        | none =>
          --no tail from the previous step so the content of the previous step is
          --a proof that a = head, so we just ignore that and return the following
          pure (← mkEqRefl e, a, .some b)
    /--
      split a sum in half, give a proof of equality and return the two halves as expressions
      the returned values will expressions representing the following `(p : e = a + b, a, b)`
      it would be easier if we could return the b reversed, but we would prefer that our sort be
      stable, and that would make the sort unstable
    -/
    halfAssociate (e : Expr) : MetaM (Expr × Expr × Option Expr) := do
      let halfLength := countSums e / 2
      if halfLength == 0
      then pure (← mkEqRefl e, e, none)
      else split halfLength e
    countSums (e : Expr) (n : Nat := 0) : Nat :=
      match_expr e with
      | HAdd.hAdd _ _ _ _ a _ => countSums a (n + 1)
      | _ => n + 1

syntax (name := reorder) "reorder" notFollowedBy("|") (ppSpace colGt term:max)*  : tactic

@[tactic reorder]
unsafe def reorderTactic : Tactic := fun stx => do
  match stx with
  | `(tactic| reorder [$args,*] ) =>
    let goal ← getMainGoal
    let target ← getMainTarget
    let varExprs ← args.getElems.mapM (elabTerm · none)
    let vars := varExprs.map Expr.fvarId!
    let .some (ring,lhs,rhs) := target.eq? | throwTacticEx `reorder goal "Expected an equality"
    let (varsReorderProof,rhsVarsReordered) ← reorderVars vars rhs
    let (termsReorderProof,expectedTarget) ← reorderTerms vars rhsVarsReordered ring
    let eqGoalMVar ← mkFreshExprMVar (← mkEq lhs expectedTarget)
    goal.assign (← mkEqTrans eqGoalMVar (← mkEqSymm (← mkEqTrans varsReorderProof termsReorderProof)))
    pushGoal eqGoalMVar.mvarId!
  | _ => throwTacticEx `reorder (← getMainGoal) "Invalid Syntax"

example (a b c : Rat) : a+b = a+b := by
  reorder [a,b,c]
  eq_refl


example (a b c : Rat) : a*b*c = c*b*a := by
  reorder [a,b,c]
  eq_refl

example (a b c : Rat) : 2*a*b*c+3*a*b = c*2*b*a+b*a*3 := by
  reorder [a,b,c]
  eq_refl

example (a b c : Rat) : 2*a*b*c+3*a*b+a+6 = 6+b*a*3+a+c*2*b*a := by
  reorder [a,b,c]
  eq_refl

example (a b c : Rat) : (2*a*b*c+3*a*b+a+6)^2 = (6+b*a*3+a+c*2*b*a)^2 := by
  reorder [a,b,c]
  eq_refl


example (a b c : Rat) : c*(2*a*b*c+3*a*b) = (c*2*b*a+b*a*3)*c := by
  reorder [a,b,c]
  eq_refl


example (a b : Rat) : a^3*b + b^6 = a^2*b*a+(b^2)^3 := by
  reorder [a,b]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul]
--  eq_refl
