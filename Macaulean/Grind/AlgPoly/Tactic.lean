/-
  `algebra_norm_reflect`: prove a polynomial identity in a commutative ring by
  reflection.

  Pipeline:

  1. reify both sides of the goal into `AlgExpr Int` plus a context of atoms;
  2. close `AlgExpr.checkPolyEq nv lhs rhs = true` with `decide +kernel`, which
     evaluates both sides to `Macaulean.Polynomial Int nv` inside the kernel;
  3. bridge `AlgExpr.denote (CertRing.ofInt A) ctx e = goalSide` in both
     directions -- `ofInt` being the ambient ring's own coefficient map, from
     its `Macaulean.CertRing` instance (`certRingData`), or the default
     subscription when it has none;
  4. chain the three with `AlgExpr.eq_of_checkPolyEq`.

  By default the whole certificate is checked by the kernel.  `+native` swaps
  step 2 for `decide +native`, which is `Lean.ofReduceBool` -- the compiler and
  its runtime join the trusted base.  It is never the default, and using it
  always logs a warning.
-/
module

public import Macaulean.Grind.AlgPoly.Reify
public meta import Macaulean.Grind.AlgPoly.Reify
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

open Lean Meta Elab Tactic

namespace Macaulean.AlgPoly.Tactic

meta section

/--
The `+native` flag, shared by every tactic in this library that ends in a
reflective certificate.  Writing it closes the `checkPolyEq … = true`
obligation with `decide +native` instead of `decide +kernel`: a compiled
computation instead of a kernel one, which puts `Lean.ofReduceBool` -- and so
the Lean compiler and its runtime -- into the proof's trusted base.  It is
never the default and using it always warns.
-/
syntax nativeFlag := " +" &"native"

initialize Lean.registerTraceClass `macaulean.reflect

/-- Above this many reified nodes, `algebra_norm` refuses to fall through to
its `simp`/`grind` finisher.  Those are superlinear and, on certificate-scale
goals, do not terminate in practice; a loud failure naming the reflective check
that went wrong is far more useful than a hang. -/
def fallbackNodeLimit : Nat := 3000

partial def exprNodeCount : Expr → Nat
  | .app f a => 1 + exprNodeCount f + exprNodeCount a
  | _ => 1

/--
Everything the reflective layer needs to know about the ambient ring, resolved
once per certificate: the `CertRing` instance, its `Grind.CommRing` parent, its
coefficient map and the proof that the map is a ring map.

Every term below is built from the *same* `certInst`, so the denotation bridge
and `AlgExpr.eq_of_checkPolyEq` agree syntactically and the bridge stays a
kernel `rfl`.
-/
structure CertRingData where
  /-- The ambient ring. -/
  ring : Expr
  /-- `CertRing ring`. -/
  certInst : Expr
  /-- `Lean.Grind.CommRing ring`, as the class's parent projection. -/
  commRingInst : Expr
  /-- `ofInt : Int → ring`. -/
  phi : Expr
  /-- `Polynomial.IsCoeffHom ofInt`. -/
  hphi : Expr

/--
Resolve the ambient ring's subscription to the certificate machinery.

A ring with a `Macaulean.CertRing` instance uses it.  A ring without one still
gets the identity check: the default subscription `CertRing.ofGrindCommRing A`
is built on the spot, and its `ofInt` is `Macaulean.intDenote A` -- exactly what
this tactic hard-wired before the class existed, so nothing that used to work
stops working, and nothing that used to be checked by the kernel now is not.
-/
def certRingData (A : Expr) : MetaM CertRingData := do
  let certTy := mkApp (mkConst ``Macaulean.CertRing) A
  let certInst ←
    match ← trySynthInstance certTy with
    | .some inst => pure inst
    | _ =>
      let commRingInst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommRing [.zero]) A)
      pure <| mkApp3 (mkConst ``Macaulean.CertRing.ofGrindCommRing) A commRingInst
        (mkConst ``Macaulean.M2BaseRing.ZZ)
  pure {
    ring := A
    certInst := certInst
    commRingInst := mkApp2 (mkConst ``Macaulean.CertRing.toCommRing) A certInst
    phi := mkApp2 (mkConst ``Macaulean.CertRing.ofInt) A certInst
    hphi := mkApp2 (mkConst ``Macaulean.CertRing.ofInt_isCoeffHom) A certInst }

/-- The term `(k : R)` as the ambient ring's own coefficient map applies it.
`Reify` recognises this shape as the coefficient `k`, which is what lets the
scaling path state `ofInt d * p = …` and still have it be a polynomial identity
in the goal's variables. -/
def CertRingData.mkOfInt (d : CertRingData) (k : Int) : Expr :=
  mkApp d.phi (Reify.intLitE k)

/-- The Macaulay2 base ring the ambient ring asks its coefficients to be
serialised into.  `whnf` rather than `evalExpr`: `CertRing` instances are
`noncomputable` (`intDenote` is), but unfolding a projection of a structure
literal is something the elaborator does anyway. -/
def CertRingData.m2BaseRing (d : CertRingData) : MetaM Macaulean.M2BaseRing := do
  let e ← whnf (mkApp2 (mkConst ``Macaulean.CertRing.m2BaseRing) d.ring d.certInst)
  if e.isConstOf ``Macaulean.M2BaseRing.QQ then pure .QQ
  else if e.isConstOf ``Macaulean.M2BaseRing.ZZ then pure .ZZ
  else throwError m!"could not evaluate the Macaulay2 base ring of{indentExpr d.ring}\
    \nit reduced to{indentExpr e}"

/-- The `CertRingRat` instance of the ambient ring, if it has subscribed to the
denominator-scaling path. -/
def certRingRatInst? (A : Expr) : MetaM (Option Expr) := do
  match ← trySynthInstance (mkApp (mkConst ``Macaulean.CertRingRat) A) with
  | .some inst => pure (some inst)
  | _ => pure none

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
        simp [Macaulean.AlgExpr.denote, Macaulean.CertRing.ofInt,
          Macaulean.CertRing.ofGrindCommRing, Macaulean.intDenote,
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

/-- Close `t = true` by kernel evaluation, or -- only when the caller asked for
it in so many words -- by native evaluation. -/
def proveBoolTrue (t : Expr) (native : Bool := false) : TacticM Expr := do
  let ty ← mkEq t (mkConst ``true)
  let mvar ← mkFreshExprMVar ty
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    if native then
      evalTactic (← `(tactic| decide +native))
    else
      evalTactic (← `(tactic| decide +kernel))
  finally
    setGoals savedGoals
  instantiateMVars mvar

/--
Build a proof of `lhs = rhs` by the reflective certificate, without touching
the goal state.  This is the whole of `algebra_norm_reflect`; tactics that
assemble a certificate themselves (`Macaulean.PolyCert`, `m2cert`) call it
directly rather than going back through tactic syntax.
-/
def proveEq (lhs rhs : Expr) (native : Bool := false) : TacticM Expr := do
  if native then
    logWarning "the reflective certificate is checked by `decide +native`: the \
      proof depends on `Lean.ofReduceBool` -- which this toolchain records as a \
      generated `._native.decide.ax` axiom -- so the Lean compiler and its \
      runtime are part of its trusted base.  Drop `+native` to have the kernel \
      check it."
  let A ← instantiateMVars (← inferType lhs)
  let uA ← Reify.getTypeLevel A
  unless uA.isZero do
    throwError m!"algebra_norm_reflect needs the ambient ring in `Type`, got `{A} : Type {uA}`"
  let crd ← certRingData A
  let commRingInst := crd.commRingInst
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
  let hChk ← proveBoolTrue checkTerm native
  let t1 ← IO.monoMsNow
  trace[macaulean.reflect] "kernel certificate: {t1 - t0} ms"
  -- 2. The two denotation bridges.
  let phi := crd.phi
  let hphi := crd.hphi
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
  pure proof

def solveGoal (native : Bool := false) : TacticM Unit := withMainContext do
  let mainGoal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let some (lhs, rhs) := getEqSides? target
    | throwError "algebra_norm_reflect only handles equality goals"
  let proof ← proveEq lhs rhs native
  mainGoal.assign proof
  setGoals ((← getGoals).erase mainGoal)

/--
`algebra_norm_reflect` proves a polynomial identity over a commutative ring by
reflection: both sides are normalized to `Macaulean.Polynomial Int nv` *inside
the kernel* and compared.  It never falls back on `simp`/`grind`, so a failure
names the reflective check that went wrong.

`algebra_norm_reflect +native` checks the certificate with `decide +native`
instead.  That is `Lean.ofReduceBool`: the proof then rests on the Lean
compiler and its runtime as well as on the kernel, so it is opt-in and always
warns.
-/
elab "algebra_norm_reflect" native:(nativeFlag)? : tactic => solveGoal native.isSome

/--
`algebra_norm` is `algebra_norm_reflect` with a `grind` fallback for small
goals (which may, unlike the reflective path, use hypotheses).  It takes the
same `+native` opt-in.
-/
elab "algebra_norm" native:(nativeFlag)? : tactic => do
  let s ← get
  try
    solveGoal native.isSome
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
