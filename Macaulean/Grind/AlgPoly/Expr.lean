/-
  `AlgExpr`: reified algebraic expressions.

  This is the syntax the reflective tactic works with: a goal `lhs = rhs` in a
  commutative ring `A` is reified into two `AlgExpr Int` trees plus a context of
  atoms, the trees are evaluated to `Macaulean.Polynomial Int nv` by the kernel,
  and the normal forms are compared.
-/
module

public import Macaulean.CASRing

@[expose] public section

namespace Macaulean

open Lean Grind CommRing

/--
An algebraic expression with coefficients in `C` over an implicit list of
variables (de Bruijn-style indices into a `Context`).

The constructors are binary and mirror the source syntax node for node; that is
what makes the tactic's denotation bridge (`AlgExpr.denote φ ctx e = goal`)
hold definitionally.
-/
inductive AlgExpr (C : Type) where
  | coeff (k : C)
  | var (i : Nat)
  | add (a b : AlgExpr C)
  | sub (a b : AlgExpr C)
  | mul (a b : AlgExpr C)
  | neg (a : AlgExpr C)
  | pow (a : AlgExpr C) (k : Nat)
  deriving Inhabited, Repr, BEq

namespace AlgExpr

/-- Denote an expression in `A`, mapping coefficients through `φ` and
variables through `ctx`. -/
def denote {C A : Type} [Grind.CommRing A] (φ : C → A) (ctx : Context A) :
    AlgExpr C → A
  | .coeff k => φ k
  | .var i => ctx.get i
  | .add a b => a.denote φ ctx + b.denote φ ctx
  | .sub a b => a.denote φ ctx - b.denote φ ctx
  | .mul a b => a.denote φ ctx * b.denote φ ctx
  | .neg a => -a.denote φ ctx
  | .pow a k => a.denote φ ctx ^ k

/-! ### Rebalancing a chain of `+` and `-`

A polynomial written out monomial by monomial reaches the reifier as a
*left-nested* chain `((t₁ + t₂) - t₃) + t₄ ⋯`, and evaluating that chain left to
right merges a one-term list into an ever-growing sorted list, which is
`O(m²)` for `m` monomials -- the single largest cost in the kernel certificate
at certificate sizes.

Flattening the chain and recombining it as a *balanced* tree makes the same
merges cost `O(m log m)`: at every level of the tree the merges touch each
monomial once, and there are `log m` levels.  On the 755-monomial benchmark
this takes building the 524-monomial remainder from 4.7 s to 1.2 s.

The rewriting is done here, on `AlgExpr`, rather than inside `toPoly`: `toPoly`
has to stay structurally recursive (the kernel must be able to unfold it), and
a chain is not a structural notion.  `denote_rebalance` says the rewriting is
denotation-preserving, which is all soundness needs.
-/

/-- Right-nested sum of a list of summands.  Only the fallback for `balFuel`;
`balance` is what callers want. -/
def sumList : List (AlgExpr Int) → AlgExpr Int
  | [] => .coeff 0
  | [a] => a
  | a :: t => .add a (sumList t)

/-- One bottom-up pairing pass: `[a, b, c, d, e] ↦ [a+b, c+d, e]`. -/
def pairUp : List (AlgExpr Int) → List (AlgExpr Int)
  | a :: b :: t => .add a b :: pairUp t
  | l => l

/-- Pair up until one summand is left.  `fuel` bounds the number of passes;
`balance` passes the length of the list, which is always enough (each pass
halves it).  The fuel-0 fallback is the plain right-nested sum, so
`balFuel f l` denotes the sum of `l` for *every* `f`. -/
def balFuel : Nat → List (AlgExpr Int) → AlgExpr Int
  | 0, l => sumList l
  | f + 1, l =>
    match l with
    | [] => .coeff 0
    | [a] => a
    | l => balFuel f (pairUp l)

/-- Combine a list of summands into a balanced `add` tree. -/
def balance (l : List (AlgExpr Int)) : AlgExpr Int := balFuel l.length l

/--
The summands of a maximal `+`/`-` chain, in order, with `a - b` contributing
`-b` and every leaf of the chain rebalanced in turn.

Written with an accumulator so that both recursive calls are on immediate
subterms: `toPoly` and this both have to be unfoldable by the kernel, which
rules out well-founded recursion.
-/
def addChain : AlgExpr Int → List (AlgExpr Int) → List (AlgExpr Int)
  | .add a b, acc => addChain a (addChain b acc)
  | .sub a b, acc => addChain a (.neg (balance (addChain b [])) :: acc)
  | .mul a b, acc => .mul (balance (addChain a [])) (balance (addChain b [])) :: acc
  | .neg a, acc => .neg (balance (addChain a [])) :: acc
  | .pow a k, acc => .pow (balance (addChain a [])) k :: acc
  | e, acc => e :: acc

/-- Rewrite every `+`/`-` chain of `e` into a balanced tree of the same
summands.  Denotation-preserving (`denote_rebalance`). -/
def rebalance (e : AlgExpr Int) : AlgExpr Int := balance (addChain e [])

end AlgExpr

/-! ### Rebalancing preserves the denotation -/

namespace AlgExpr

section

variable {A : Type} [Grind.CommRing A] {φ : Int → A}
  (hφ : Polynomial.IsCoeffHom φ) (ctx : Context A)

/-- The sum of a list of summands, as an element of `A`. -/
def denoteList (φ : Int → A) (ctx : Context A) : List (AlgExpr Int) → A
  | [] => 0
  | a :: t => a.denote φ ctx + denoteList φ ctx t

@[simp] theorem denoteList_nil : denoteList φ ctx [] = 0 := rfl

@[simp] theorem denoteList_cons (a : AlgExpr Int) (t : List (AlgExpr Int)) :
    denoteList φ ctx (a :: t) = a.denote φ ctx + denoteList φ ctx t := rfl

include hφ

theorem denote_sumList : ∀ (l : List (AlgExpr Int)),
    (sumList l).denote φ ctx = denoteList φ ctx l := by
  intro l
  induction l with
  | nil => exact hφ.map_zero
  | cons a t ih =>
    cases t with
    | nil => exact (Grind.Semiring.add_zero _).symm
    | cons b t' =>
      show a.denote φ ctx + (sumList (b :: t')).denote φ ctx
        = a.denote φ ctx + denoteList φ ctx (b :: t')
      rw [ih]

theorem denoteList_pairUp : ∀ (l : List (AlgExpr Int)),
    denoteList φ ctx (pairUp l) = denoteList φ ctx l := by
  intro l
  induction l using pairUp.induct with
  | case1 a b t ih =>
    show (a.denote φ ctx + b.denote φ ctx) + denoteList φ ctx (pairUp t) = _
    rw [ih, Grind.AddCommMonoid.add_assoc]
    rfl
  | case2 l hne =>
    match l, hne with
    | [], _ => rfl
    | [_], _ => rfl
    | a :: b :: t, hne => exact absurd rfl (hne a b t)

theorem denote_balFuel : ∀ (f : Nat) (l : List (AlgExpr Int)),
    (balFuel f l).denote φ ctx = denoteList φ ctx l := by
  intro f
  induction f with
  | zero => exact denote_sumList hφ ctx
  | succ f ih =>
    intro l
    match l with
    | [] => exact hφ.map_zero
    | [a] => exact (Grind.Semiring.add_zero _).symm
    | a :: b :: t =>
      show (balFuel f (pairUp (a :: b :: t))).denote φ ctx = _
      rw [ih, denoteList_pairUp hφ ctx]

theorem denote_balance (l : List (AlgExpr Int)) :
    (balance l).denote φ ctx = denoteList φ ctx l :=
  denote_balFuel hφ ctx _ l

/-- The chain of an expression sums to the expression. -/
theorem denoteList_addChain : ∀ (e : AlgExpr Int) (acc : List (AlgExpr Int)),
    denoteList φ ctx (addChain e acc) = e.denote φ ctx + denoteList φ ctx acc := by
  intro e
  induction e with
  | coeff k => intro acc; rfl
  | var i => intro acc; rfl
  | add a b iha ihb =>
    intro acc
    show denoteList φ ctx (addChain a (addChain b acc)) = _
    rw [iha, ihb, ← Grind.AddCommMonoid.add_assoc]
    rfl
  | sub a b iha ihb =>
    intro acc
    show denoteList φ ctx (addChain a (.neg (balance (addChain b [])) :: acc)) = _
    rw [iha, denoteList_cons]
    show a.denote φ ctx + (-(balance (addChain b [])).denote φ ctx
      + denoteList φ ctx acc) = _
    rw [denote_balance hφ ctx, ihb, denoteList_nil, Grind.Semiring.add_zero,
      ← Grind.AddCommMonoid.add_assoc]
    show _ = a.denote φ ctx - b.denote φ ctx + _
    rw [Grind.Ring.sub_eq_add_neg]
  | mul a b iha ihb =>
    intro acc
    show denoteList φ ctx
      (.mul (balance (addChain a [])) (balance (addChain b [])) :: acc) = _
    show (balance (addChain a [])).denote φ ctx * (balance (addChain b [])).denote φ ctx
      + denoteList φ ctx acc = _
    rw [denote_balance hφ ctx, denote_balance hφ ctx, iha, ihb, denoteList_nil,
      Grind.Semiring.add_zero, Grind.Semiring.add_zero]
    rfl
  | neg a iha =>
    intro acc
    show denoteList φ ctx (.neg (balance (addChain a [])) :: acc) = _
    show -(balance (addChain a [])).denote φ ctx + denoteList φ ctx acc = _
    rw [denote_balance hφ ctx, iha, denoteList_nil, Grind.Semiring.add_zero]
    rfl
  | pow a k iha =>
    intro acc
    show denoteList φ ctx (.pow (balance (addChain a [])) k :: acc) = _
    show (balance (addChain a [])).denote φ ctx ^ k + denoteList φ ctx acc = _
    rw [denote_balance hφ ctx, iha, denoteList_nil, Grind.Semiring.add_zero]
    rfl

/-- **Rebalancing is denotation-preserving.**  This is all that the reflective
checker needs from it: the chain is reassociated, and `a - b` is read as
`a + (-b)`, both of which hold in any commutative ring. -/
theorem denote_rebalance (e : AlgExpr Int) :
    (rebalance e).denote φ ctx = e.denote φ ctx := by
  rw [rebalance, denote_balance hφ ctx, denoteList_addChain hφ ctx, denoteList_nil,
    Grind.Semiring.add_zero]

end

end AlgExpr

end Macaulean

end
