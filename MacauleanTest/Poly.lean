--import Macaulean
import MRDI
import Lean
import Macaulean.IdealMembership

open Lean.Grind.CommRing
open Lean.Grind

def w : Expr := .var 0
def x : Expr := .var 1
def y : Expr := .var 2
def z : Expr := .var 3

instance : Add Expr where
  add a b := .add a b
instance : Sub Expr where
  sub a b := .sub a b
instance : Neg Expr where
  neg a := .neg a
instance : Mul Expr where
  mul a b := .mul a b
instance : HPow Expr Nat Expr where
  hPow a k := .pow a k
instance : OfNat Expr n where
  ofNat := .num n

def f := x^5 + y^5 + z^5 + w^5 - 5*x*y*z*w |>.toPoly

def g := x*y*z*w*(x + y + z + w) |>.toPoly

/-- info: f : Poly -/
#guard_msgs in
#check f

/--
info: Poly.add (Int.ofNat 1)
  (Mon.mult { x := 0, k := 2 }
    (Mon.mult { x := 1, k := 1 } (Mon.mult { x := 2, k := 1 } (Mon.mult { x := 3, k := 1 } Mon.unit))))
  (Poly.add (Int.ofNat 1)
    (Mon.mult { x := 0, k := 1 }
      (Mon.mult { x := 1, k := 2 } (Mon.mult { x := 2, k := 1 } (Mon.mult { x := 3, k := 1 } Mon.unit))))
    (Poly.add (Int.ofNat 1)
      (Mon.mult { x := 0, k := 1 }
        (Mon.mult { x := 1, k := 1 } (Mon.mult { x := 2, k := 2 } (Mon.mult { x := 3, k := 1 } Mon.unit))))
      (Poly.add (Int.ofNat 1)
        (Mon.mult { x := 0, k := 1 }
          (Mon.mult { x := 1, k := 1 } (Mon.mult { x := 2, k := 1 } (Mon.mult { x := 3, k := 2 } Mon.unit))))
        (Poly.num (Int.ofNat 0)))))
-/
#guard_msgs in
#reduce g

--TODO make this into a proper test
def test : Poly :=
  .add 3 .unit <| .add 5 (.mult ⟨2, 3⟩ <| .unit) <| .num 0

/--
info: {"data": [[3, []], [5, [[2, 3]]], [0, []]],
 "_type": "Lean.Grind.CommRing.Poly",
 "_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.26.0-rc1"]}}
-/
#guard_msgs in
#eval (Lean.toJson <$> toMrdi (m := Id) test).run' .empty

#eval (do
  let .ok mrdiJson ← Lean.fromJson? <$> Lean.toJson <$> toMrdi test | return .error "Incorrect MRDI"
  fromMrdi? (m := Id) (α := Poly) mrdiJson).run' .empty


--TODO make this into a proper test
def test2Poly : Poly :=
  .add 3 (.mult ⟨0,1⟩ <| .mult ⟨2,2⟩ .unit) <| .add 1 (.mult ⟨0, 1⟩ <| .mult ⟨1,2⟩ .unit) <| .num 1
def test2Coefficients : Std.TreeMap Var Rat :=
  .ofList [(0,(1:Rat)/2)]

def test2 : ConcretePoly Rat := ⟨test2Poly, test2Coefficients⟩

/--
info: {"data":
 {"poly": "bf9837e6-468a-41df-a270-aea8d4a747e8",
  "coefficients": [[0, [1, 2]]]},
 "_type": {"params": "Rat", "name": "ConcretePoly"},
 "_refs":
 {"bf9837e6-468a-41df-a270-aea8d4a747e8":
  {"data": [[3, [[0, 1], [2, 2]]], [1, [[0, 1], [1, 2]]], [1, []]],
   "_type": "Lean.Grind.CommRing.Poly"}},
 "_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.26.0-rc1"]}}
-/
#guard_msgs in
#eval (do
  let mrdi ← (toMrdi test2)
  pure <| Lean.toJson mrdi).run' .empty

#eval (do
  let mrdi ← (toMrdi test2)
  let .ok mrdiJson := Lean.fromJson? <| Lean.toJson mrdi | return .error "Invalid JSON"
  let .ok val ← fromMrdi? (m := Id) (α := ConcretePoly Rat) mrdiJson | return .error "Failed to decode"
  pure <| Except.ok (val == test2)).run' .empty
