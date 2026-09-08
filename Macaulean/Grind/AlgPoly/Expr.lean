/-
  `AlgExpr`: reified algebraic expressions.

  This is the syntax the reflective tactic works with: a goal `lhs = rhs` in a
  commutative ring `A` is reified into two `AlgExpr Int` trees plus a context of
  atoms, the trees are evaluated to `Macaulean.Polynomial Int nv` by the kernel,
  and the normal forms are compared.
-/
import Macaulean.Polynomial.Hom

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

end AlgExpr

/-! ### The canonical coefficient map `Int → A` -/

/--
The canonical coefficient map `Int → A`.

`Lean.Grind.CommRing.denoteInt` is grind's own canonical map: it produces
`OfNat.ofNat |k|` (negated when `k < 0`) through grind's numeral instance, which
is exactly what makes the tactic's denotation bridge reduce to the goal's own
numerals.  Packaging it as a named definition keeps the `Grind.Ring` instance
argument in one place, so the term the tactic emits and the term
`intDenote_isCoeffHom` talks about are syntactically identical.
-/
noncomputable def intDenote (A : Type) [Grind.CommRing A] : Int → A :=
  fun k => Grind.CommRing.denoteInt k

theorem intDenote_isCoeffHom (A : Type) [Grind.CommRing A] :
    Polynomial.IsCoeffHom (intDenote A) where
  map_zero := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_zero
  map_one := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_one
  map_add a b := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_add a b
  map_mul a b := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_mul a b
  map_neg a := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_neg a

end Macaulean
