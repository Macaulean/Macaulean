/-
  Reification: a goal expression in a commutative ring `A` becomes an
  `AlgExpr Int` tree (built directly as an `Expr`, as a literal constructor
  tree) plus a context of atoms.

  Integer literals become `AlgExpr.coeff`; `+`, `-`, `*`, unary `-` and `^` with
  a `Nat` literal exponent become the corresponding constructors; everything
  else is an atom.  The tree mirrors the source term node for node, which is
  what makes the tactic's denotation bridge hold definitionally.

  The classification itself (`classify`) and the atom table (`AtomState`,
  `mkAtom`) are shared with the Macaulay2 half of the library, which reifies
  the same terms into `Macaulean.Polynomial` instead
  (`Macaulean/IdealMembership.lean`).  One definition of "atom" for both is not
  a tidiness point: a certificate Macaulay2 produces in *its* variables has to
  be checkable by the kernel in *these* ones.
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

/-- The inverse of `intLitE`, plus the shapes `Meta.getIntValue?` already
knows.  `getIntValue?` does *not* read the raw constructor form -- it wants an
`OfNat`/`Neg` application -- and the constructor form is exactly what the
tactics build, so both have to be tried. -/
def intLitValue? (e : Expr) : MetaM (Option Int) := do
  match_expr e with
  | Int.ofNat n => pure <| (← getNatValue? n).map Int.ofNat
  | Int.negSucc n => pure <| (← getNatValue? n).map fun k => Int.negSucc k
  | _ => getIntValue? e

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

/-! ### The atom table

Both halves of the library -- the reflective checker below, and the Macaulay2
round trip in `Macaulean/IdealMembership.lean` -- have to agree on *what a
variable is*, or a certificate obtained by one cannot be checked by the other.
There is therefore one atom table and one classifier, here, and two thin
recursions over them. -/

/-- The atoms discovered so far, in first-occurrence order, with a cache from
the syntactic forms already seen to their index.  The order is what makes
`m2cert?`'s printed `in [...]` clause reproducible. -/
structure AtomState where
  atoms : Array Expr := #[]
  atomMap : Std.HashMap Expr Nat := {}

abbrev AtomM := StateT AtomState MetaM

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

/-- The index of `e` in the atom table, registering it if it is new.  A new
atom is appended, so indices follow first occurrence. -/
def mkAtom (e : Expr) : AtomM Nat := do
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

/-! ### The classifier -/

/--
What one node of a ring expression is, as far as this library is concerned.

Everything that is not one of the five ring operations or an integer
coefficient is an `atom` -- a maximal non-arithmetic subterm.  A free variable
is not special: `x`, `MvPolynomial.X 0` and `f x y` are all atoms, and are
identified up to definitional equality by `mkAtom`.
-/
inductive Node where
  /-- `a + b`. -/
  | add (a b : Expr)
  /-- `a - b`. -/
  | sub (a b : Expr)
  /-- `a * b`. -/
  | mul (a b : Expr)
  /-- `-a`. -/
  | neg (a : Expr)
  /-- `a ^ k` with a `Nat` literal exponent. -/
  | pow (a : Expr) (k : Nat)
  /-- An integer coefficient: a numeral, a cast of one, or the ambient ring's
  own `CASRing.ofInt` applied to one. -/
  | coeff (k : Int)
  /-- A maximal non-arithmetic subterm. -/
  | atom

/--
Classify one node.  This is the *single* definition of "ring operation",
"coefficient" and "atom" in the library: `reify` below turns it into an
`AlgExpr`, and `toPolynomialExpr` (`Macaulean/IdealMembership.lean`) turns it
into a `Macaulean.Polynomial` for Macaulay2.  If the two ever disagreed, a
certificate obtained from Macaulay2 could not be checked by the kernel.
-/
def classify (e : Expr) : MetaM Node := do
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => pure <| .add a b
  | HSub.hSub _ _ _ _ a b => pure <| .sub a b
  | HMul.hMul _ _ _ _ a b => pure <| .mul a b
  | Neg.neg _ _ a => pure <| .neg a
  | HPow.hPow _ _ _ _ a b =>
    match (← getNatValue? b) with
    | some k => pure <| .pow a k
    | none => pure .atom
  | IntCast.intCast _ _ a =>
    match (← getIntValue? a) with
    | some k => pure <| .coeff k
    | none => pure .atom
  | Macaulean.CASRing.ofInt _ _ a =>
    -- The coefficient map of the ambient ring's own `CASRing` instance.  The
    -- scaling path (`poly_cert … / d`) states its identity with an explicit
    -- `ofInt d` factor, and it has to count as the *coefficient* `d` rather
    -- than as an atom -- `d * (p - r) = Σ qᵢ' gᵢ` is a polynomial identity in
    -- the goal's variables only, not in `d`.  Reifying it as a coefficient is
    -- also what makes the denotation bridge `rfl`: the tactic's `φ` is this
    -- very projection.
    match (← intLitValue? a) with
    | some k => pure <| .coeff k
    | none => pure .atom
  | NatCast.natCast _ _ a =>
    match (← getNatValue? a) with
    | some k => pure <| .coeff (Int.ofNat k)
    | none => pure .atom
  | OfNat.ofNat _ n _ =>
    match (← getNatValue? n) with
    | some k => pure <| .coeff (Int.ofNat k)
    | none => pure .atom
  | _ => pure .atom

partial def reify (e : Expr) : AtomM Expr := do
  match ← liftM (classify e) with
  | .add a b => pure <| mkCtor ``Macaulean.AlgExpr.add #[← reify a, ← reify b]
  | .sub a b => pure <| mkCtor ``Macaulean.AlgExpr.sub #[← reify a, ← reify b]
  | .mul a b => pure <| mkCtor ``Macaulean.AlgExpr.mul #[← reify a, ← reify b]
  | .neg a => pure <| mkCtor ``Macaulean.AlgExpr.neg #[← reify a]
  | .pow a k => pure <| mkCtor ``Macaulean.AlgExpr.pow #[← reify a, mkRawNatLit k]
  | .coeff k => pure <| mkCoeff k
  | .atom => mkVar <$> mkAtom e

/--
Walk `e` for its atoms only, registering each in the table.  Used to learn the
variable count before building anything that needs it -- `Polynomial R nv`
mentions `nv` in its type, so the Macaulay2 side has to know it up front.
-/
partial def collectAtoms (e : Expr) : AtomM Unit := do
  match ← liftM (classify e) with
  | .add a b | .sub a b | .mul a b => collectAtoms a; collectAtoms b
  | .neg a => collectAtoms a
  | .pow a _ => collectAtoms a
  | .coeff _ => pure ()
  | .atom => discard <| mkAtom e

/-- The atoms of `es`, in first-occurrence order, left to right. -/
def atomStateOf (es : Array Expr) : MetaM AtomState := do
  let (_, s) ← (es.forM collectAtoms).run {}
  pure s

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
