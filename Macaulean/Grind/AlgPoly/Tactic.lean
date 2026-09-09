/-
  `algebra_norm_reflect`: prove a polynomial identity in a commutative ring by
  reflection.

  Pipeline:

  1. reify both sides of the goal into `AlgExpr Int` plus a context of atoms;
  2. close `AlgExpr.checkPolyEq nv lhs rhs = true` with `decide +kernel`, which
     evaluates both sides to `Macaulean.Polynomial Int nv` inside the kernel;
  3. bridge `AlgExpr.denote (intDenote A) ctx e = goalSide` in both directions;
  4. chain the three with `AlgExpr.eq_of_checkPolyEq`.

  Never `native_decide`, never `+native`: the whole certificate is checked by
  the kernel.
-/
module

public import Macaulean.Grind.AlgPoly.Reify
public meta import Macaulean.Grind.AlgPoly.Reify
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

open Lean Meta Elab Tactic

namespace Macaulean.AlgPoly.Tactic

meta section

initialize Lean.registerTraceClass `macaulean.reflect

/-- Above this many reified nodes, `algebra_norm` refuses to fall through to
its `simp`/`grind` finisher.  Those are superlinear and, on certificate-scale
goals, do not terminate in practice; a loud failure naming the reflective check
that went wrong is far more useful than a hang. -/
def fallbackNodeLimit : Nat := 3000

partial def exprNodeCount : Expr → Nat
  | .app f a => 1 + exprNodeCount f + exprNodeCount a
  | _ => 1

def getEqSides? (target : Expr) : Option (Expr × Expr) :=
  match target.getAppFn with
  | .const ``Eq _ =>
    let args := target.getAppArgs
    if args.size == 3 then some (args[1]!, args[2]!) else none
  | _ => none

/--
Prove `lhs = rhs` by handing `Eq.refl lhs`, *ascribed* to `lhs = rhs`, to the
kernel via `mkAuxLemma` -- the same trick `decide +kernel` uses.  The kernel
then does the defeq check with full unfolding, which is 200-300x cheaper than
asking `Meta.isDefEq` to do it when the relevant definitions are not exposed at
the ambient transparency.
-/
def mkKernelRfl (lhs rhs : Expr) : TacticM Expr := do
  let type ← mkEq lhs rhs
  let value ← mkEqRefl lhs
  let levelsInType := (collectLevelParams {} type).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let lemmaName ← withOptions (Elab.async.set · false) do
    mkAuxLemma lemmaLevels type value
  pure <| mkConst lemmaName (lemmaLevels.map .param)

/-- The `simp`/`grind` bridge, kept only for goals where the kernel `rfl` does
not apply (unusual numeral shapes, `smul`, …).  Quadratic-or-worse at
certificate scale. -/
def simpBridge (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  let run : TacticM Unit := do
    try
      evalTactic (← `(tactic| rfl))
    catch _ =>
      evalTactic (← `(tactic|
        simp [Macaulean.AlgExpr.denote, Macaulean.intDenote,
          Lean.Grind.CommRing.denoteInt_eq, Lean.RArray.get, Nat.ble]))
      if !(← getGoals).isEmpty then
        evalTactic (← `(tactic| grind))
        evalTactic (← `(tactic| done))
  try
    run
  finally
    setGoals savedGoals
  instantiateMVars mvar

/-- The denotation bridge: kernel-checked `rfl` first, `simp`/`grind` only if
that fails. -/
def proveBridge (lhs rhs : Expr) : TacticM Expr := do
  try
    mkKernelRfl lhs rhs
  catch _ =>
    simpBridge lhs rhs

/-- Close `t = true` by kernel evaluation. -/
def proveBoolTrue (t : Expr) : TacticM Expr := do
  let ty ← mkEq t (mkConst ``true)
  let mvar ← mkFreshExprMVar ty
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic (← `(tactic| decide +kernel))
  finally
    setGoals savedGoals
  instantiateMVars mvar

def solveGoal : TacticM Unit := withMainContext do
  let mainGoal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some (lhs, rhs) := getEqSides? target
    | throwError "algebra_norm_reflect only handles equality goals"
  let A ← instantiateMVars (← inferType lhs)
  let uA ← Reify.getTypeLevel A
  unless uA.isZero do
    throwError m!"algebra_norm_reflect needs the ambient ring in `Type`, got `{A} : Type {uA}`"
  let commRingInst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommRing [.zero]) A)
  let reified ← Reify.runPair lhs rhs
  let nv := reified.atoms.size
  let ctx ← Reify.mkContextExpr A reified.atoms
  let nvE := mkRawNatLit nv
  trace[macaulean.reflect] "reified {nv} atoms"
  -- Monomials are packed into a single `Nat` key in base `Mon.base nv`
  -- (`Macaulean/Polynomial/Key.lean`).  Check natively, before handing anything
  -- to the kernel, that a whole key still fits in Lean's small-`Nat` range:
  -- past that the kernel falls off the GMP fast path and the certificate gets
  -- slow rather than wrong.
  let bits := max 8 (62 / max 1 nv)
  unless (2 ^ bits) ^ nv < 2 ^ 62 do
    logWarning m!"algebra_norm_reflect: {nv} variables need a {bits * nv}-bit \
      monomial key, past the kernel's small-`Nat` range; the certificate will \
      still be checked, but slowly."
  trace[macaulean.reflect] "monomial key base 2^{bits}, {bits * nv} bits"
  -- 1. The certificate, checked by the kernel.
  let checkTerm := mkAppN (mkConst ``Macaulean.AlgExpr.checkPolyEq)
    #[nvE, reified.lhsReified, reified.rhsReified]
  let t0 ← IO.monoMsNow
  let hChk ← proveBoolTrue checkTerm
  let t1 ← IO.monoMsNow
  trace[macaulean.reflect] "kernel certificate: {t1 - t0} ms"
  -- 2. The two denotation bridges.
  let phi := mkApp2 (mkConst ``Macaulean.intDenote) A commRingInst
  let hphi := mkApp2 (mkConst ``Macaulean.intDenote_isCoeffHom) A commRingInst
  let denoteFn := mkConst ``Macaulean.AlgExpr.denote
  let denoteLhs := mkAppN denoteFn
    #[Reify.intTypeE, A, commRingInst, phi, ctx, reified.lhsReified]
  let denoteRhs := mkAppN denoteFn
    #[Reify.intTypeE, A, commRingInst, phi, ctx, reified.rhsReified]
  let hLhs ←
    try proveBridge denoteLhs lhs
    catch e => throwError m!"lhs denotation bridge failed: {e.toMessageData}"
  let hRhs ←
    try proveBridge denoteRhs rhs
    catch e => throwError m!"rhs denotation bridge failed: {e.toMessageData}"
  let t2 ← IO.monoMsNow
  trace[macaulean.reflect] "denotation bridges: {t2 - t1} ms"
  -- 3. Chain them.
  let core := mkAppN (mkConst ``Macaulean.AlgExpr.eq_of_checkPolyEq)
    #[A, commRingInst, phi, hphi, ctx, nvE, reified.lhsReified, reified.rhsReified, hChk]
  let proof ← mkEqTrans (← mkEqSymm hLhs) (← mkEqTrans core hRhs)
  let proof ← instantiateMVars proof
  if proof.hasMVar then
    throwError m!"reflective proof has metavariables: {proof}"
  mainGoal.assign proof
  setGoals ((← getGoals).erase mainGoal)

/--
`algebra_norm_reflect` proves a polynomial identity over a commutative ring by
reflection: both sides are normalized to `Macaulean.Polynomial Int nv` *inside
the kernel* and compared.  It never falls back on `simp`/`grind`, so a failure
names the reflective check that went wrong.
-/
elab "algebra_norm_reflect" : tactic => solveGoal

/--
`algebra_norm` is `algebra_norm_reflect` with a `grind` fallback for small
goals (which may, unlike the reflective path, use hypotheses).
-/
elab "algebra_norm" : tactic => do
  let s ← get
  try
    solveGoal
    return
  catch e =>
    set s
    let target ← instantiateMVars (← getMainTarget)
    if exprNodeCount target > fallbackNodeLimit then
      throwError m!"algebra_norm: reflective normalization did not close this goal, \
and it is too large for the `grind` fallback.\n{e.toMessageData}"
  evalTactic (← `(tactic| grind))

end

end Macaulean.AlgPoly.Tactic

end
