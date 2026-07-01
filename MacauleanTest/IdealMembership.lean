import Lean
import Macaulean.IdealMembership

open Lean Grind Elab Tactic Meta

--Tests for some of the components of the IdealMembership code

/--
info: some (((CommRing.Expr.var 0).mul (CommRing.Expr.var 1)).add ((CommRing.Expr.num 2).mul (CommRing.Expr.var 2)).neg)
-/
#guard_msgs in
#eval do
  let ringType := mkConst ``Rat
  withLocalDecl `x .default ringType fun x =>
    withLocalDecl `y .default ringType fun y => do
      let c1 : Expr := toExpr (1/2 : Rat)
      let c2 : Expr := toExpr (2 : Rat)
      let expr ← mkAdd (← mkMul c1 x) (← mkAppM `Neg.neg #[← mkMul c2 y])
      (toCommRingExpr? expr).run' .empty

/--
info:  3   *   1  /  2   *   y   ^   2   +   1  /  2   *   x   ^   2
-/
#guard_msgs in
#eval do
  let ringType := mkConst ``Rat
  withLocalDecl `x .default ringType fun x =>
    withLocalDecl `y .default ringType fun y => do
      let poly : CommRing.Poly :=
        .add 3 (.mult ⟨0,1⟩ <| .mult ⟨2,2⟩ .unit) <| .add 1 (.mult ⟨0, 1⟩ <| .mult ⟨1,2⟩ .unit) <| .num 0
      let exprPoly : ExprPoly := {
        poly := poly
        coefficients := .ofList [(0,toExpr (1/2 : Rat))]
      }
      let vars := Std.TreeMap.ofList [(1, x), (2, y)]
      let expr ← exprFromPoly (reindex := false) ringType vars exprPoly
      let exprSyntax ← PrettyPrinter.delab expr
      pure <| Syntax.prettyPrint exprSyntax

--this theorem really should be proven elsewhere
private theorem RArray_get_ofArray (h : i < arr.size) : (RArray.ofArray arr len_hyp).get i = arr[i] := by
  have irw : i = ↑(Fin.mk i h) := by simp
  conv =>
    left
    right
    rw [irw]
  rw [RArray.ofArray, RArray.get_ofFn]
  simp

example {x y : Rat} (f : 1/2*x + 1/2*y = 0) (g : 1/2*x + 1/2*y = 0) : (x + y)^2 = 0 := by
  m2idealmem +grind [f]


example {x y : Rat} (f : 2*x= 0) (g : 3*y = 0) : (x + y)^4 = 0 := by
  m2idealmem +grind [f,g]

example {x y : Rat} (f : 2*x= 0) (g : 3*y = 0) : (x + y)^4 = 0 := by
  m2idealmem -grind [f,g]
  clear f g
  grind

example {x y z : Rat} (f : 2*x= 0) (g : 3*y = 0) (h : y+z=0) : (x + y + z)^4 = 0 := by
  m2idealmem +grind [f, g, h]

-- determinential ideal example
-- this is the ideal of 2x2 minors of a generic 3x3 **symmetric** matrix
example {a b c d e f : Rat}
  (f1 : e^2-d*f = 0) (f2 : c*e-b*f = 0) (f3 : c*d-b*e = 0)
  (f4 : c^2-a*f = 0) (f5 : b*c-a*e = 0) (f6 : b^2 - a*d = 0) :
    (c^2*d-2*b*c*e+a*e^2+b^2*f-a*d*f = 0) := by
  m2idealmem [f1,f2,f3,f4,f5,f6]
  clear f1 f2 f3 f4 f5 f6
  grind


variable {R : Type} [CommRing R] [ToExpr R]
instance : Std.Associative (α := R) (.*.) := ⟨Semiring.mul_assoc⟩
instance : Std.Commutative (α := R) (.*.) := ⟨CommRing.mul_comm⟩

instance : Std.Associative (α := R) (.+.) := ⟨Semiring.add_assoc⟩
instance : Std.Commutative (α := R) (.+.) := ⟨Semiring.add_comm⟩


-- TODO reconsider this test, it should be a failing test, but what should the error be?
-- /--
-- error: Could not show equality
-- R : Type
-- inst✝¹ : CommRing R
-- inst✝ : ToExpr R
-- x y z : R
-- f : 2 * x = 0
-- g : y = 0
-- h : y + z = 0
-- ⊢ (x + y + z) ^ 4 =
--     0 + 0 * (2 * x) +
--         (6 * x ^ 2 * y + 4 * x * y ^ 2 + y ^ 3 + 6 * x ^ 2 * z + 12 * x * y * z + 4 * y ^ 2 * z + 8 * x * z ^ 2 +
--               6 * y * z ^ 2 +
--             3 * z ^ 3) *
--           y +
--       (4 * x ^ 3 + 6 * x ^ 2 * z + 4 * x * z ^ 2 + z ^ 3) * (y + z)
-- -/
-- #guard_msgs in
-- example {x y z : R} (f : 2*x = 0) (g : y = 0) (h : y+z=0) : (x + y + z)^4 = 0 := by
--   m2idealmem -grind [f, g, h]
--   fail_if_success grind
--   fail "Could not show equality"

example {x y z : Rat} (f : 2*x = 0) (g : y = 0) (h : y+z=0) : (x + y + z)^4 = 0 := by
  m2idealmem -grind [f, g, h]
  clear f g h
  simp [Macaulean.Polynomial.denote, Macaulean.Mon.denote, RArray_get_ofArray]
  grind
