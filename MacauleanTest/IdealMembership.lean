import Lean
import Macaulean.IdealMembership

open Lean Grind Elab Tactic Meta

--Tests for some of the components of the IdealMembership code

/--
info: some (((CommRing.Expr.var 0).mul (CommRing.Expr.var 1)).add (CommRing.Expr.var 2))
-/
#guard_msgs in
#eval do
  let ringType := mkConst ``Rat
  withLocalDecl `x .default ringType fun x =>
    withLocalDecl `y .default ringType fun y => do
      let c : Expr := toExpr (1/2 : Rat)
      let expr ← mkAdd (← mkMul c x) y
      (toCommRingExpr? expr).run' .empty

/--
info:  ↑  3   *   1  /  2   *   y   ^   2   +   ↑  1   *   1  /  2   *   x   ^   2   +   ↑  0
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

example {x y : Rat} (f : 1/2*x + 1/2*y = 0) (g : 1/2*x + 1/2*y = 0) : (x + y)^2 = 0 := by
  m2idealmem [f]


example {x y : Rat} (f : 2*x= 0) (g : 3*y = 0) : (x + y)^4 = 0 := by
  m2idealmem [f]
