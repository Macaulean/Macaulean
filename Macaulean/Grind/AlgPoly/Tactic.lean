/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Macaulean.Grind.AlgPoly.Reify
public import Macaulean.Grind.AlgPoly.Denote
public import Macaulean.Grind.AlgPoly.Kronecker
public import Macaulean.Grind.AlgPoly.KroneckerMod
public import Macaulean.Grind.Algebra.Instances
public meta import Macaulean.Grind.AlgPoly.Reify
public meta import Macaulean.Grind.AlgPoly.Denote
public meta import Macaulean.Grind.AlgPoly.Kronecker
public meta import Macaulean.Grind.AlgPoly.KroneckerMod
public meta import Macaulean.Grind.Algebra.Instances
public meta import Lean.Elab.Tactic.Basic

@[expose] public section

/-!
# algebra_norm tactic

Verifies polynomial identities in algebras with two-level normalization.

## Strategy

1. **Default: the GMP-free reflective path.**  When every coefficient of the
   reified goal is an integer literal, normalize with residue-vector
   coefficients (`ModVec`) and close the goal with
   `AlgExpr.eq_of_checkModZero`.  Every `Nat`/`Int` the kernel then computes
   with stays below `2^62`, so the check never reaches GMP; see the audit in
   `Macaulean/Grind/AlgPoly/KroneckerMod.lean`.
2. Fall back to the exact-integer Kronecker path
   (`AlgExpr.eq_of_toKPoly_eq`), which is what `set_option macaulean.gmpFree
   false` selects outright.  That path is fine mathematically but has the
   kernel do big-integer arithmetic.
3. Then the two-level `AlgPoly` normal form, and finally (only in
   `algebra_norm`, never in `algebra_norm_reflect`) the `grind`/`simp`
   pipeline.
-/

open Lean Meta Elab Tactic

meta section

initialize Lean.registerTraceClass `macaulean.reflect

register_option macaulean.gmpFree : Bool := {
  defValue := true
  descr := "algebra_norm_reflect: try the GMP-free residue-vector (single-pass CRT) certificate before the exact-integer Kronecker certificate.  Set to false to use the exact-integer path directly."
}

end

namespace Macaulean.AlgPoly.Tactic

open Lean.Grind

meta section

namespace Reflect
structure Inputs where
  R : Expr
  A : Expr
  algebraMapFn : Expr
  algebraInst : Expr
  lhs : Expr
  rhs : Expr
  lhsReified : Expr
  rhsReified : Expr
  coeffVars : Array Expr
  ambientVars : Array Expr

def findAlgebraMapFn? (e : Expr) : Option Expr :=
  match e.find? fun sub =>
      sub.isApp &&
      let fn := sub.appFn!
      match fn.getAppFn with
      | .const ``Lean.Grind.algebraMap _ => fn.getAppNumArgs == 5
      | _ => false with
  | some app => some app.appFn!
  | none => none

def getEqSides? (target : Expr) : Option (Expr × Expr) :=
  match target.getAppFn with
  | .const ``Eq _ =>
    let args := target.getAppArgs
    if args.size == 3 then some (args[1]!, args[2]!) else none
  | _ => none

def buildInputs (target : Expr) : TacticM Inputs := do
  let some (lhs, rhs) := getEqSides? target
    | throwError "reflective algebra_norm only handles equality goals"
  let (algebraMapFn, R, A, algebraInst) ←
    match findAlgebraMapFn? target with
    | some algebraMapFn => do
      let .const ``Lean.Grind.algebraMap _ := algebraMapFn.getAppFn
        | throwError "unexpected algebraMap head"
      let args := algebraMapFn.getAppArgs
      pure (algebraMapFn, args[0]!, args[1]!, args[4]!)
    | none => do
      -- No `algebraMap` in the goal: view `A` as an algebra over itself
      -- (`Algebra.selfAlgebra`), so plain commutative-ring identities are
      -- handled by the same two-level pipeline (numerals become coefficients).
      let A ← instantiateMVars (← inferType lhs)
      let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
      let csInst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommSemiring [uA]) A)
      let sInst ← synthInstance (mkApp (mkConst ``Lean.Grind.Semiring [uA]) A)
      let algInst := mkApp2 (mkConst ``Lean.Grind.Algebra.selfAlgebra [uA]) A csInst
      let fn := mkApp5 (mkConst ``Lean.Grind.algebraMap [uA, uA]) A A csInst sInst algInst
      pure (fn, A, A, algInst)
  let reified ← Macaulean.AlgPoly.Reify.runAmbientPair algebraMapFn lhs rhs
  pure {
    R, A, algebraMapFn, algebraInst, lhs, rhs,
    lhsReified := reified.lhsAlgExpr,
    rhsReified := reified.rhsAlgExpr,
    coeffVars := reified.coeffVars,
    ambientVars := reified.ambientVars
  }

/-! ### Helpers for the GMP-free (residue-vector) path -/

/--
Moduli pool: the 32 largest primes below `2^31`.

Each is `> 2^30`, so `k` of them certify coefficients up to `2^(30k)`; each is
`< 2^31`, so a product of two residues is `< 2^62` and the kernel stays on the
boxed-scalar fast path.  Only a prefix is ever used, and the Bézout table the
tactic emits is re-checked by the kernel, so this list is data, not trust.
-/
def modPool : Array Nat :=
  #[2147483647, 2147483629, 2147483587, 2147483579, 2147483563, 2147483549,
    2147483543, 2147483497, 2147483489, 2147483477, 2147483423, 2147483399,
    2147483353, 2147483323, 2147483269, 2147483249, 2147483237, 2147483179,
    2147483171, 2147483137, 2147483123, 2147483077, 2147483069, 2147483059,
    2147483053, 2147483033, 2147483029, 2147482951, 2147482949, 2147482943,
    2147482937, 2147482921]

/-- Extended Euclid, at meta level (native `Nat`/`Int`; GMP here is harmless). -/
partial def egcd (a b : Nat) : Nat × Int × Int :=
  if a == 0 then (b, 0, 1)
  else
    let (g, x, y) := egcd (b % a) a
    (g, y - ((b / a : Nat) : Int) * x, x)

/-- Bézout witness `(a, b)` with `a * m = b * n + 1`, `0 < a < n` and `b < m`
(so both products are below `2^62` for moduli below `2^31`). -/
def bezWitness (m n : Nat) : Nat × Nat :=
  let (_, x, _) := egcd m n
  let a := (((x % (n : Int)) + (n : Int)) % (n : Int)).toNat
  let a := if a == 0 then n else a
  (a, (a * m - 1) / n)

/-- Row `i` of the table holds the witnesses for `ms[i]` against `ms[i+1:]`. -/
def bezTable : List Nat → List (List (Nat × Nat))
  | [] => []
  | m :: ms => ms.map (fun n => bezWitness m n) :: bezTable ms

def natTypeE : Expr := mkConst ``Nat
def intTypeE : Expr := mkConst ``Int
def natPairTypeE : Expr := mkApp2 (mkConst ``Prod [0, 0]) natTypeE natTypeE
def rowTypeE : Expr := mkApp (mkConst ``List [0]) natPairTypeE

/-- `Int` literal in constructor form, which the kernel reduces without going
through `OfNat`/`Neg` instances. -/
def intLitE (k : Int) : Expr :=
  if k < 0 then mkApp (mkConst ``Int.negSucc) (mkRawNatLit (k.natAbs - 1))
  else mkApp (mkConst ``Int.ofNat) (mkRawNatLit k.toNat)

def mkListE (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty x acc)
    (mkApp (mkConst ``List.nil [0]) ty)

def mkNatListE (l : List Nat) : Expr := mkListE natTypeE (l.map mkRawNatLit)

def mkNatPairE (p : Nat × Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0]) natTypeE natTypeE (mkRawNatLit p.1) (mkRawNatLit p.2)

def mkTblE (t : List (List (Nat × Nat))) : Expr :=
  mkListE rowTypeE (t.map fun r => mkListE natPairTypeE (r.map mkNatPairE))

/-- Build the `Expr` for an `AlgExpr Int` value (a literal constructor tree). -/
def mkAlgIntE : Macaulean.AlgExpr Int → Expr
  | .coeff k => mkApp2 (mkConst ``Macaulean.AlgExpr.coeff [.zero]) intTypeE (intLitE k)
  | .var i => mkApp2 (mkConst ``Macaulean.AlgExpr.var [.zero]) intTypeE (mkRawNatLit i)
  | .add a b =>
    mkApp3 (mkConst ``Macaulean.AlgExpr.add [.zero]) intTypeE (mkAlgIntE a) (mkAlgIntE b)
  | .mul a b =>
    mkApp3 (mkConst ``Macaulean.AlgExpr.mul [.zero]) intTypeE (mkAlgIntE a) (mkAlgIntE b)
  | .sub a b =>
    mkApp3 (mkConst ``Macaulean.AlgExpr.sub [.zero]) intTypeE (mkAlgIntE a) (mkAlgIntE b)
  | .neg a => mkApp2 (mkConst ``Macaulean.AlgExpr.neg [.zero]) intTypeE (mkAlgIntE a)
  | .pow a k =>
    mkApp3 (mkConst ``Macaulean.AlgExpr.pow [.zero]) intTypeE (mkAlgIntE a) (mkRawNatLit k)

/-- A grind `Poly` that is a constant. -/
def polyConst? : Lean.Grind.CommRing.Poly → Option Int
  | .num k => some k
  | .add k m p =>
    if m == Lean.Grind.CommRing.Mon.unit then (polyConst? p).map (k + ·) else none

/-- Re-coefficient a reified expression from grind `Poly` to `Int`; `none` when
some coefficient is not a plain integer (e.g. it mentions a coefficient-ring
variable coming through `algebraMap`). -/
def toAlgIntE? : Macaulean.AlgExpr Lean.Grind.CommRing.Poly → Option (Macaulean.AlgExpr Int)
  | .coeff p => (polyConst? p).map .coeff
  | .var i => some (.var i)
  | .add a b => match toAlgIntE? a, toAlgIntE? b with
    | some x, some y => some (.add x y)
    | _, _ => none
  | .mul a b => match toAlgIntE? a, toAlgIntE? b with
    | some x, some y => some (.mul x y)
    | _, _ => none
  | .sub a b => match toAlgIntE? a, toAlgIntE? b with
    | some x, some y => some (.sub x y)
    | _, _ => none
  | .neg a => (toAlgIntE? a).map .neg
  | .pow a k => (toAlgIntE? a).map (.pow · k)

/-- `2^62`: the largest power of two whose products of two operands still fit in
Lean's boxed-scalar range. -/
def scalarBound : Nat := 4611686018427387904

/-- Every coefficient literal is below `2^62` in absolute value, so `Int.natAbs`
and `Int.emod` on it stay on the scalar path. -/
def coeffsSmall : Macaulean.AlgExpr Int → Bool
  | .coeff k => k.natAbs < scalarBound
  | .var _ => true
  | .add a b | .mul a b | .sub a b => coeffsSmall a && coeffsSmall b
  | .neg a => coeffsSmall a
  | .pow a _ => coeffsSmall a

/-- Node count of a reified expression tree (it is a literal tree, so no
sharing to worry about). -/
partial def exprNodeCount : Expr → Nat
  | .app f a => 1 + exprNodeCount f + exprNodeCount a
  | _ => 1

/-- Above this many nodes, `algebra_norm_reflect` refuses to fall through to the
cons-list `AlgPoly` normal form and its `simp`/`grind` finisher.  Those are
superlinear and, on certificate-scale goals, do not terminate in practice; a
loud failure naming the reflective check that went wrong is far more useful
than a hang.  Small goals (including ones that need `grind` to use a
hypothesis) are unaffected. -/
def fallbackNodeLimit : Nat := 3000

/-- `D ^ nv < bound`, by a multiplication loop that stops early. -/
def powLt (D : Nat) : Nat → Nat → Bool
  | 0, bound => 1 < bound
  | n + 1, bound =>
    let r := powLtVal D n bound
    match r with
    | some v => v * D < bound
    | none => false
where
  powLtVal (D : Nat) : Nat → Nat → Option Nat
    | 0, bound => if 1 < bound then some 1 else none
    | n + 1, bound =>
      match powLtVal D n bound with
      | some v => let w := v * D; if w < bound then some w else none
      | none => none

def proveDefinallyEq (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic (← `(tactic| rfl))
  finally
    setGoals savedGoals
  instantiateMVars mvar

partial def proveNormalizedDenoteEq (A : Expr) (coeffPolyDenote : Expr) (ambientCtx : Expr)
    (lhs rhs : Macaulean.AlgPoly Lean.Grind.CommRing.Poly) : TacticM Expr := do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel A
  let ringAType := mkApp (mkConst ``Lean.Grind.Ring [uA]) A
  let ringAInst ← synthInstance ringAType
  let polyDenoteFn := mkConst ``Macaulean.AlgPoly.denote [.zero, uA]
  let lhsExpr := mkAppN polyDenoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      A,
      ringAInst,
      coeffPolyDenote,
      ambientCtx,
      Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr lhs
    ]
  let rhsExpr := mkAppN polyDenoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      A,
      ringAInst,
      coeffPolyDenote,
      ambientCtx,
      Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr rhs
    ]
  let goalType ← mkEq lhsExpr rhsExpr
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  try
    evalTactic (← `(tactic|
      simp [
        Macaulean.AlgPoly.denote,
        Lean.Grind.CommRing.Poly.denote,
        Lean.Grind.CommRing.Mon.denote,
        Lean.Grind.CommRing.Mon.denote_ofVar,
        Lean.Grind.CommRing.Power.denote_eq,
        Lean.Grind.CommRing.Var.denote,
        Lean.RArray.get,
        Nat.ble,
        Lean.Grind.Algebra.algebraMap_add,
        Lean.Grind.Algebra.algebraMap_sub,
        Lean.Grind.Algebra.algebraMap_mul,
        Lean.Grind.Algebra.algebraMap_neg,
        Lean.Grind.Algebra.algebraMap_zero,
        Lean.Grind.Algebra.algebraMap_one,
        Lean.Grind.Semiring.zero_mul,
        Lean.Grind.AddCommMonoid.zero_add
      ]))
    if !(← getGoals).isEmpty then
      evalTactic (← `(tactic| grind))
      evalTactic (← `(tactic| done))
  finally
    setGoals savedGoals
  instantiateMVars mvar

/--
Bridge the reflective denotation back to the goal.

Reification mirrors the goal expression node for node, and coefficients denote
through `Lean.Grind.CommRing.denoteInt`, which produces the goal's own numeral
`OfNat.ofNat` applications; so over concrete rings the bridge holds
definitionally and `rfl` closes it in time linear in the expression.  The
`simp`/`grind` route is kept only as a last resort for goals where that fails;
it is quadratic-or-worse at certificate scale, so `bridgeStrict` refuses it.
-/
def proveBridge (bridgeStrict : Bool) (lhs rhs : Expr) : TacticM Expr := do
  let goalType ← mkEq lhs rhs
  let mvar ← mkFreshExprMVar goalType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  let simpBridge : TacticM Unit := do
    evalTactic (← `(tactic|
      simp [
        Macaulean.AlgExpr.denote,
        Lean.Grind.CommRing.Expr.denote,
        Lean.Grind.CommRing.Expr.denote_toPoly,
        Lean.Grind.CommRing.denoteInt_eq,
        Lean.Grind.CommRing.Var.denote,
        Lean.RArray.get,
        Nat.ble,
        Lean.Grind.Algebra.algebraMap_add,
        Lean.Grind.Algebra.algebraMap_sub,
        Lean.Grind.Algebra.algebraMap_mul,
        Lean.Grind.Algebra.algebraMap_neg,
        Lean.Grind.Algebra.algebraMap_zero,
        Lean.Grind.Algebra.algebraMap_one,
        Lean.Grind.Algebra.algebraMap_self
      ]))
    if !(← getGoals).isEmpty then
      evalTactic (← `(tactic| grind))
      evalTactic (← `(tactic| done))
  let run : TacticM Unit := do
    try
      evalTactic (← `(tactic| rfl))
    catch e =>
      if bridgeStrict then
        throwError m!"denotation bridge is not closed by `rfl`: {e.toMessageData}"
      simpBridge
  try
    run
  finally
    setGoals savedGoals
  instantiateMVars mvar

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

/--
The GMP-free certificate.

Reify as usual, then re-coefficient the reified expressions from grind `Poly`
to `Int` (possible exactly when every coefficient of the goal is an integer
literal), and prove the identity with `AlgExpr.eq_of_checkModZero`: the kernel
normalizes `e₁ - e₂` once with residue-vector coefficients modulo `k` primes in
`[2^30, 2^31)` and checks the result is zero, plus an a priori `L¹` bound
showing that a coefficient divisible by all `k` moduli must vanish.

Everything the kernel evaluates stays below `2^62`.  The choices made here (the
Kronecker base `D`, the digit count `nv`, the moduli, the Bézout witnesses) are
all re-checked by the kernel, so a bad choice makes the tactic fail, never
succeed wrongly.
-/
unsafe def proveModPath (inputs : Inputs) : TacticM Expr := withMainContext do
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel inputs.A
  let commRingAInst ← synthInstance (mkApp (mkConst ``Lean.Grind.CommRing [uA]) inputs.A)
  let ambientCtx ← liftM <| Macaulean.AlgPoly.Reify.mkContextExpr inputs.A inputs.ambientVars
  let algExprPolyType := mkApp (mkConst ``Macaulean.AlgExpr [.zero])
    Macaulean.AlgPoly.Reify.polyType
  let lhsVal ← evalExpr (Macaulean.AlgExpr Lean.Grind.CommRing.Poly)
    algExprPolyType inputs.lhsReified
  let rhsVal ← evalExpr (Macaulean.AlgExpr Lean.Grind.CommRing.Poly)
    algExprPolyType inputs.rhsReified
  let some lhsInt := toAlgIntE? lhsVal
    | throwError "GMP-free path: the left-hand side has a non-integer coefficient"
  let some rhsInt := toAlgIntE? rhsVal
    | throwError "GMP-free path: the right-hand side has a non-integer coefficient"
  let eSub := Macaulean.AlgExpr.sub lhsInt rhsInt
  unless coeffsSmall eSub do
    throwError "GMP-free path: a coefficient is at least 2^62, so the kernel \
would need bignum arithmetic"
  let nv := inputs.ambientVars.size
  let dBase := Nat.max lhsInt.degBound rhsInt.degBound + 2
  unless powLt dBase nv scalarBound do
    throwError m!"GMP-free path: the packed monomial keys would exceed 2^62 \
(base {dBase}, {nv} variables)"
  let bnd := eSub.ubnd
  unless bnd.m < 2147483648 do
    throwError "GMP-free path: internal error, unnormalized coefficient bound"
  let k := (31 + bnd.e + 29) / 30
  unless k ≤ modPool.size do
    throwError m!"GMP-free path: would need {k} moduli, only {modPool.size} available"
  let ms := modPool.toList.take k
  let tbl := bezTable ms
  unless Macaulean.pairwiseCoprimeB ms tbl do
    throwError "GMP-free path: internal error, bad Bézout table"
  unless Macaulean.allBig ms do
    throwError "GMP-free path: internal error, modulus below 2^30"
  unless Macaulean.AlgExpr.boundOk ms eSub do
    throwError "GMP-free path: internal error, coefficient bound check failed"
  unless Macaulean.AlgExpr.checkModZero dBase nv ms eSub do
    throwError m!"residue-vector normal forms differ (base {dBase}, {nv} \
variables, {k} moduli)"
  trace[macaulean.reflect] "GMP-free certificate: Kronecker base {dBase}, \
{nv} variables, {k} moduli (coefficient bound < 2^{31 + bnd.e})"
  let e1E := mkAlgIntE lhsInt
  let e2E := mkAlgIntE rhsInt
  let eSubE := mkApp3 (mkConst ``Macaulean.AlgExpr.sub [.zero]) intTypeE e1E e2E
  let msE := mkNatListE ms
  let tblE := mkTblE tbl
  let dE := mkRawNatLit dBase
  let nvE := mkRawNatLit nv
  let phi := mkApp2 (mkConst ``Macaulean.intDenote [uA]) inputs.A commRingAInst
  let hphi := mkApp2 (mkConst ``Macaulean.intDenote_isRingHom [uA]) inputs.A commRingAInst
  let denoteFn := mkConst ``Macaulean.AlgExpr.denote [.zero, uA]
  let denoteLhs := mkAppN denoteFn #[intTypeE, inputs.A, commRingAInst, phi, ambientCtx, e1E]
  let denoteRhs := mkAppN denoteFn #[intTypeE, inputs.A, commRingAInst, phi, ambientCtx, e2E]
  let hLhs ← proveBridge true denoteLhs inputs.lhs
  let hRhs ← proveBridge true denoteRhs inputs.rhs
  let hcop ← proveBoolTrue (mkApp2 (mkConst ``Macaulean.pairwiseCoprimeB) msE tblE)
  let hbig ← proveBoolTrue (mkApp (mkConst ``Macaulean.allBig) msE)
  let hchk ← proveBoolTrue
    (mkAppN (mkConst ``Macaulean.AlgExpr.checkModZero) #[dE, nvE, msE, eSubE])
  let hbnd ← proveBoolTrue (mkApp2 (mkConst ``Macaulean.AlgExpr.boundOk) msE eSubE)
  let core := mkAppN (mkConst ``Macaulean.AlgExpr.eq_of_checkModZero [uA])
    #[inputs.A, commRingAInst, phi, ambientCtx, hphi, dE, nvE, msE, tblE, e1E, e2E,
      hcop, hbig, hchk, hbnd]
  let hLhsSymm ← mkEqSymm hLhs
  mkEqTrans hLhsSymm (← mkEqTrans core hRhs)

unsafe def proveReifiedEq (inputs : Inputs) : TacticM Expr := withMainContext do
  let coeffCtx ← liftM <| Macaulean.AlgPoly.Reify.mkContextExpr inputs.R inputs.coeffVars
  let ambientCtx ← liftM <| Macaulean.AlgPoly.Reify.mkContextExpr inputs.A inputs.ambientVars
  let uR ← Macaulean.AlgPoly.Reify.getTypeLevel inputs.R
  let uA ← Macaulean.AlgPoly.Reify.getTypeLevel inputs.A
  let commRingRType := mkApp (mkConst ``Lean.Grind.CommRing [uR]) inputs.R
  let commRingAType := mkApp (mkConst ``Lean.Grind.CommRing [uA]) inputs.A
  let commRingRInst ← synthInstance commRingRType
  let commRingAInst ← synthInstance commRingAType
  let ringRType := mkApp (mkConst ``Lean.Grind.Ring [uR]) inputs.R
  let ringAType := mkApp (mkConst ``Lean.Grind.Ring [uA]) inputs.A
  let ringRInst ← synthInstance ringRType
  let ringAInst ← synthInstance ringAType
  let coeffPolyDenote := mkLambda `p .default Macaulean.AlgPoly.Reify.polyType <|
    mkApp inputs.algebraMapFn <|
      mkAppN (mkConst ``Lean.Grind.CommRing.Poly.denote [uR])
        #[inputs.R, ringRInst, coeffCtx, mkBVar 0]
  let hφ := mkAppN (mkConst ``Macaulean.AlgPoly.Reify.polyCoeffIsRingHom)
      #[inputs.R, inputs.A, commRingRInst, commRingAInst, inputs.algebraInst, coeffCtx]
  let coeffRingPolyInst ← synthInstance
    (mkApp (mkConst ``Macaulean.CoeffRing [.zero]) Macaulean.AlgPoly.Reify.polyType)
  let lhsPoly := mkAppN (mkConst ``Macaulean.AlgExpr.toAlgPoly [.zero])
    #[Macaulean.AlgPoly.Reify.polyType, coeffRingPolyInst, inputs.lhsReified]
  let rhsPoly := mkAppN (mkConst ``Macaulean.AlgExpr.toAlgPoly [.zero])
    #[Macaulean.AlgPoly.Reify.polyType, coeffRingPolyInst, inputs.rhsReified]
  let denoteFn := mkConst ``Macaulean.AlgExpr.denote [.zero, uA]
  let polyDenoteFn := mkConst ``Macaulean.AlgPoly.denote [.zero, uA]
  let denoteLhs := mkAppN denoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      inputs.A,
      commRingAInst,
      coeffPolyDenote,
      ambientCtx,
      inputs.lhsReified
    ]
  let denoteRhs := mkAppN denoteFn
    #[
      Macaulean.AlgPoly.Reify.polyType,
      inputs.A,
      commRingAInst,
      coeffPolyDenote,
      ambientCtx,
      inputs.rhsReified
    ]
  let hLhs ←
    try
      proveBridge false denoteLhs inputs.lhs
    catch e =>
      throwError m!"lhs bridge failed: {e.toMessageData}"
  let hRhs ←
    try
      proveBridge false denoteRhs inputs.rhs
    catch e =>
      throwError m!"rhs bridge failed: {e.toMessageData}"
  -- Fast path: Kronecker-packed normal form (single-`Nat` monomial keys), which
  -- is what scales to certificate identities with ~10³ monomials.  The base and
  -- digit count are chosen here but re-checked by guards inside `checkKEq`, so
  -- a bad choice fails over to the other strategies rather than being trusted.
  let kCore : Option Expr ← (do
    try
      let algExprType := mkApp (mkConst ``Macaulean.AlgExpr [.zero])
        Macaulean.AlgPoly.Reify.polyType
      let lhsVal ← evalExpr (Macaulean.AlgExpr Lean.Grind.CommRing.Poly)
        algExprType inputs.lhsReified
      let rhsVal ← evalExpr (Macaulean.AlgExpr Lean.Grind.CommRing.Poly)
        algExprType inputs.rhsReified
      let nv := inputs.ambientVars.size
      let dBase := Nat.max lhsVal.degBound rhsVal.degBound + 2
      -- Native pre-check: fail over quickly (and informatively) before asking
      -- the kernel to evaluate a normalization that will not succeed.
      if !Macaulean.AlgExpr.checkKEq dBase nv lhsVal rhsVal then
        throwError "Kronecker normal forms differ (base {dBase}, {nv} variables)"
      let checkTerm := mkAppN (mkConst ``Macaulean.AlgExpr.checkKEq [.zero])
        #[Macaulean.AlgPoly.Reify.polyType, coeffRingPolyInst,
          mkNatLit dBase, mkNatLit nv, inputs.lhsReified, inputs.rhsReified]
      let checkEqTrue ← mkEq checkTerm (mkConst ``true)
      let hChkMVar ← mkFreshExprMVar checkEqTrue
      let savedGoals ← getGoals
      setGoals [hChkMVar.mvarId!]
      try
        evalTactic (← `(tactic| decide +kernel))
      finally
        setGoals savedGoals
      let hChk ← instantiateMVars hChkMVar
      pure <| some <| mkAppN (mkConst ``Macaulean.AlgExpr.eq_of_toKPoly_eq [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          inputs.A,
          coeffRingPolyInst,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          mkNatLit dBase,
          mkNatLit nv,
          inputs.lhsReified,
          inputs.rhsReified,
          hChk
        ]
    catch _ =>
      pure none)
  if let some core := kCore then
    let hLhsSymm ← mkEqSymm hLhs
    let hCoreRhs ← mkEqTrans core hRhs
    return (← mkEqTrans hLhsSymm hCoreRhs)
  try
    let beqTerm ← mkAppM ``BEq.beq #[lhsPoly, rhsPoly]
    let beqEq ← mkEq beqTerm (mkConst ``true)
    let hBeqMVar ← mkFreshExprMVar beqEq
    let savedGoals ← getGoals
    setGoals [hBeqMVar.mvarId!]
    try
      evalTactic (← `(tactic| decide +kernel))
    finally
      setGoals savedGoals
    let hBeq ← instantiateMVars hBeqMVar
    let core :=
      mkAppN (mkConst ``Macaulean.AlgExpr.eq_of_toAlgPoly_eq [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          inputs.A,
          coeffRingPolyInst,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          inputs.lhsReified,
          inputs.rhsReified,
          hBeq
        ]
    let hLhsSymm ← mkEqSymm hLhs
    let hCoreRhs ← mkEqTrans core hRhs
    mkEqTrans hLhsSymm hCoreRhs
  catch beqErr =>
    let size := exprNodeCount inputs.lhsReified + exprNodeCount inputs.rhsReified
    if size > fallbackNodeLimit then
      throwError m!"reflective normalization did not close this goal \
({size} reified nodes); refusing the `simp`/`grind` fallback at this size.\n\
{beqErr.toMessageData}"
    let algPolyType := mkApp (mkConst ``Macaulean.AlgPoly [.zero]) Macaulean.AlgPoly.Reify.polyType
    let lhsNorm ← evalExpr (Macaulean.AlgPoly Lean.Grind.CommRing.Poly) algPolyType lhsPoly
    let rhsNorm ← evalExpr (Macaulean.AlgPoly Lean.Grind.CommRing.Poly) algPolyType rhsPoly
    let lhsNormExpr := Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr lhsNorm
    let rhsNormExpr := Macaulean.AlgPoly.Reify.mkAlgPolyValueExpr rhsNorm
    let lhsNormDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        lhsNormExpr
      ]
    let rhsNormDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        rhsNormExpr
      ]
    let lhsPolyDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        lhsPoly
      ]
    let rhsPolyDenote := mkAppN polyDenoteFn
      #[
        Macaulean.AlgPoly.Reify.polyType,
        inputs.A,
        ringAInst,
        coeffPolyDenote,
        ambientCtx,
        rhsPoly
      ]
    let core ←
      try
        proveNormalizedDenoteEq inputs.A coeffPolyDenote ambientCtx lhsNorm rhsNorm
      catch e =>
        throwError m!"normalized denotation proof failed: {e.toMessageData}"
    let hNormLhs ←
      try
        proveDefinallyEq lhsNormDenote lhsPolyDenote
      catch e =>
        throwError m!"lhs normalization bridge failed: {e.toMessageData}"
    let hNormRhs ←
      try
        proveDefinallyEq rhsNormDenote rhsPolyDenote
      catch e =>
        throwError m!"rhs normalization bridge failed: {e.toMessageData}"
    let hToPolyLhs :=
      mkAppN (mkConst ``Macaulean.AlgExpr.denote_toAlgPoly [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          coeffRingPolyInst,
          inputs.A,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          inputs.lhsReified
        ]
    let hToPolyRhs :=
      mkAppN (mkConst ``Macaulean.AlgExpr.denote_toAlgPoly [.zero, uA])
        #[
          Macaulean.AlgPoly.Reify.polyType,
          coeffRingPolyInst,
          inputs.A,
          commRingAInst,
          coeffPolyDenote,
          ambientCtx,
          hφ,
          inputs.rhsReified
        ]
    let hNormLhsGoal ← mkEqTrans hNormLhs hToPolyLhs
    let hNormRhsGoal ← mkEqTrans hNormRhs hToPolyRhs
    let hNormLhsGoal ← mkEqTrans hNormLhsGoal hLhs
    let hNormRhsGoal ← mkEqTrans hNormRhsGoal hRhs
    let hNormLhsGoalSymm ← mkEqSymm hNormLhsGoal
    let hCoreRhs ← mkEqTrans core hNormRhsGoal
    mkEqTrans hNormLhsGoalSymm hCoreRhs

unsafe def solveGoal : TacticM Unit := withMainContext do
  let mainGoal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let inputs ← buildInputs target
  let gmpFree := macaulean.gmpFree.get (← getOptions)
  let proof0 ←
    if gmpFree then
      try
        proveModPath inputs
      catch modErr =>
        let modMsg := modErr.toMessageData
        try
          proveReifiedEq inputs
        catch e =>
          throwError m!"GMP-free certificate failed: {modMsg}\n\
            exact-integer certificate failed: {e.toMessageData}"
    else
      proveReifiedEq inputs
  let proof ← instantiateMVars proof0
  if proof.hasMVar then
    throwError m!"reflective proof has metavariables: {proof}"
  mainGoal.assign proof
  setGoals ((← getGoals).erase mainGoal)

end Reflect

unsafe def reflectOnly : TacticM Unit := do
  let s ← get
  let mut directErr : MessageData := m!""
  try
    Reflect.solveGoal
    return
  catch e =>
    directErr := e.toMessageData
    set s
  try
    evalTactic (← `(tactic| simp only [Lean.Grind.Algebra.algebraMap_smul_def]))
    if (← getGoals).isEmpty then
      return
  catch e =>
    throwError m!"algebra_norm_reflect could not solve the goal\n\
      direct attempt: {directErr}\n\
      after smul preprocessing: {e.toMessageData}"
  try
    Reflect.solveGoal
    return
  catch e =>
    set s
    let _ := e
    throwError m!"algebra_norm_reflect could not solve the goal\n\
      direct attempt: {directErr}\n\
      after smul preprocessing: reflective normalization failed"

elab "algebra_norm_reflect" : tactic => do
  unsafe do
    reflectOnly

elab "algebra_norm" : tactic => do
  unsafe do
    let s ← get
    try
      reflectOnly
      return
    catch _ =>
      set s
    -- Fallback 1: try grind directly (handles hypotheses, simple identities)
    try
      evalTactic (← `(tactic| grind))
      return
    catch _ => pure ()
    -- Fallback 2: contract algebraMap products/sums + grind
    try
      evalTactic (← `(tactic|
        (simp (config := { maxSteps := 200000 }) only [
          ← Lean.Grind.Algebra.algebraMap_mul, ← Lean.Grind.Algebra.algebraMap_add,
          ← Lean.Grind.Algebra.algebraMap_sub, ← Lean.Grind.Semiring.mul_assoc,
          ← Lean.Grind.Semiring.right_distrib,
          Lean.Grind.Algebra.algebraMap_smul_def];
         grind)))
      return
    catch _ => pure ()
    -- Fallback 3: expand algebraMap via simp, then grind
    evalTactic (← `(tactic|
      (simp (config := { maxSteps := 200000 }) only [
        Lean.Grind.Algebra.algebraMap_add, Lean.Grind.Algebra.algebraMap_mul,
        Lean.Grind.Algebra.algebraMap_sub, Lean.Grind.Algebra.algebraMap_neg,
        Lean.Grind.Algebra.algebraMap_zero, Lean.Grind.Algebra.algebraMap_one,
        Lean.Grind.Algebra.algebraMap_smul_def];
       grind)))

end

end Macaulean.AlgPoly.Tactic

end
