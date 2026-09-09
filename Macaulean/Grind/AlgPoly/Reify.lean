/-
  Reification: a goal expression in a commutative ring `A` becomes an
  `AlgExpr Int` tree (built directly as an `Expr`, as a literal constructor
  tree) plus a context of atoms.

  Integer literals become `AlgExpr.coeff`; `+`, `-`, `*`, unary `-` and `^` with
  a `Nat` literal exponent become the corresponding constructors; everything
  else is an atom.  The tree mirrors the source term node for node, which is
  what makes the tactic's denotation bridge hold definitionally.
-/
module

public import Macaulean.Grind.AlgPoly.PolyEval
public import Lean.Data.RArray
public meta import Macaulean.Grind.AlgPoly.PolyEval
public meta import Lean.Data.RArray
public meta import Lean.Meta.Basic
public meta import Lean.Meta.SynthInstance

@[expose] public section

open Lean Meta

namespace Macaulean.AlgPoly.Reify

meta section

def intTypeE : Expr := mkConst ``Int

def algExprIntType : Expr := mkApp (mkConst ``Macaulean.AlgExpr) intTypeE

/-- `Int` literal in constructor form, which the kernel reduces without going
through `OfNat`/`Neg` instances. -/
def intLitE (k : Int) : Expr :=
  if k < 0 then mkApp (mkConst ``Int.negSucc) (mkRawNatLit (k.natAbs - 1))
  else mkApp (mkConst ``Int.ofNat) (mkRawNatLit k.toNat)

def mkCtor (declName : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst declName) (#[intTypeE] ++ args)

def mkCoeff (k : Int) : Expr := mkCtor ``Macaulean.AlgExpr.coeff #[intLitE k]

def mkVar (i : Nat) : Expr := mkCtor ``Macaulean.AlgExpr.var #[mkRawNatLit i]

/-- The universe level `u` of `type : Type u`. -/
def getTypeLevel (type : Expr) : MetaM Level := do
  let u' ← getLevel type
  pure <| match u' with
    | .succ u => u
    | u => u

def mkNatZero (type : Expr) : MetaM Expr := do
  let u ← getTypeLevel type
  let semiringInstType := mkApp (mkConst ``Lean.Grind.Semiring [u]) type
  let semiringInst ← synthInstance semiringInstType
  let natCastInst := mkApp2 (mkConst ``Lean.Grind.Semiring.natCast [u]) type semiringInst
  pure <| mkApp3 (mkConst ``NatCast.natCast [u]) type natCastInst (mkNatLit 0)

/-- Build the `Context A` (a `Lean.RArray`) for the reified atoms. -/
def mkContextExpr (type : Expr) (vars : Array Expr) : MetaM Expr := do
  if h : 0 < vars.size then
    Lean.RArray.toExpr type id (Lean.RArray.ofFn (vars[·]) h)
  else
    Lean.RArray.toExpr type id (Lean.RArray.leaf (← mkNatZero type))

structure State where
  atoms : Array Expr := #[]
  atomMap : Std.HashMap Expr Nat := {}

abbrev ReifyM := StateT State MetaM

/-- Find an already-registered atom that is *definitionally* equal to `e`.

Syntactic equality is not enough: the same mathematical atom routinely reaches
the reifier in several syntactic forms (differing instance paths, differing
`NeZero` proofs inside `Fin.instOfNat`, …).  Splitting one atom into two
variables is not unsound -- the normal forms simply differ -- but it makes the
tactic *fail*.  A defeq scan over the (very few) registered atoms costs nothing
and keeps the atom set minimal. -/
def findDefEqAtom (atoms : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  for h : i in [0 : atoms.size] do
    if ← isDefEq atoms[i] e then
      return some i
  return none

def mkAtom (e : Expr) : ReifyM Nat := do
  let s ← get
  match s.atomMap[e]? with
  | some idx => pure idx
  | none =>
    match ← liftM (findDefEqAtom s.atoms e) with
    | some idx =>
      modify fun s => { s with atomMap := s.atomMap.insert e idx }
      pure idx
    | none =>
      let idx := s.atoms.size
      modify fun s => { s with
        atoms := s.atoms.push e
        atomMap := s.atomMap.insert e idx }
      pure idx

partial def reify (e : Expr) : ReifyM Expr := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b =>
    pure <| mkCtor ``Macaulean.AlgExpr.add #[← reify a, ← reify b]
  | HSub.hSub _ _ _ _ a b =>
    pure <| mkCtor ``Macaulean.AlgExpr.sub #[← reify a, ← reify b]
  | HMul.hMul _ _ _ _ a b =>
    pure <| mkCtor ``Macaulean.AlgExpr.mul #[← reify a, ← reify b]
  | Neg.neg _ _ a =>
    pure <| mkCtor ``Macaulean.AlgExpr.neg #[← reify a]
  | HPow.hPow _ _ _ _ a b =>
    match (← getNatValue? b) with
    | some k => pure <| mkCtor ``Macaulean.AlgExpr.pow #[← reify a, mkRawNatLit k]
    | none => mkVar <$> mkAtom e
  | IntCast.intCast _ _ a =>
    match (← getIntValue? a) with
    | some k => pure <| mkCoeff k
    | none => mkVar <$> mkAtom e
  | NatCast.natCast _ _ a =>
    match (← getNatValue? a) with
    | some k => pure <| mkCoeff (Int.ofNat k)
    | none => mkVar <$> mkAtom e
  | OfNat.ofNat _ n _ =>
    match (← getNatValue? n) with
    | some k => pure <| mkCoeff (Int.ofNat k)
    | none => mkVar <$> mkAtom e
  | _ =>
    mkVar <$> mkAtom e

structure PairResult where
  lhsReified : Expr
  rhsReified : Expr
  atoms : Array Expr

def runPair (lhs rhs : Expr) : MetaM PairResult := do
  let ((l, r), s) ← (do
      let l ← reify lhs
      let r ← reify rhs
      pure (l, r)).run {}
  pure { lhsReified := l, rhsReified := r, atoms := s.atoms }

end

end Macaulean.AlgPoly.Reify

end
