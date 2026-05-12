--import Macaulean
import MRDI
import Lean
import Macaulean.IdealMembership
import Macaulean.Polynomial

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
info: {"data": [["3", []], ["5", [["2", "3"]]], ["0", []]],
 "_type": "Lean.Grind.CommRing.Poly",
 "_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.29.1"]}}
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
  "coefficients": [["0", ["1", "2"]]]},
 "_type": {"params": "Rat", "name": "ConcretePoly"},
 "_refs":
 {"bf9837e6-468a-41df-a270-aea8d4a747e8":
  {"data":
   [["3", [["0", "1"], ["2", "2"]]],
    ["1", [["0", "1"], ["1", "2"]]],
    ["1", []]],
   "_type": "Lean.Grind.CommRing.Poly"}},
 "_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.29.1"]}}
-/
#guard_msgs in
#eval (do
  let mrdi ← (toMrdi test2)
  pure <| Lean.toJson mrdi).run' .empty


/--
info: {"data":
 [[["2", "1"], [2, 0, 4]],
  [["1", "1"], [1, 1, 5]],
  [["2", "1"], [2, 1, 2]],
  [["1", "1"], [1, 2, 3]]],
 "_type": {"params": "Rat", "name": "Polynomial"},
 "_ns": {"Lean": ["https://github.com/leanprover/lean4", "4.29.1"]}}
-/
#guard_msgs in
#eval runMrdiIO (m := IO) <| do
  let mrdiData ← toMrdi <|
    (Macaulean.Polynomial.mk [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,2]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,1,0]⟩]) *
    (Macaulean.Polynomial.mk [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [1,0,2]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,1,3]⟩])
  pure <| Lean.toJson mrdiData

example : (Macaulean.Polynomial.mk [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,2]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,1,0]⟩]) *
    (Macaulean.Polynomial.mk [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [1,0,2]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,1,3]⟩]) =
    (Macaulean.Polynomial.mk [
      ⟨2, .ofPowers [2,0,4]⟩,
      ⟨1, .ofPowers [1,1,5]⟩,
      ⟨2, .ofPowers [2,1,2]⟩,
      ⟨1, .ofPowers [1,2,3]⟩]) := by
  simp only [HMul.hMul, Mul.mul]
  simp +decide +arith [Macaulean.Polynomial.mul, Rat.mul_def']
  decide +kernel

/--
info: { terms := [{ coefficient := 2, monomial := { powers := [1, 0, 1, 0], powers_length := _ } },
            { coefficient := 2, monomial := { powers := [0, 1, 1, 0], powers_length := _ } },
            { coefficient := 1, monomial := { powers := [1, 0, 0, 1], powers_length := _ } },
            { coefficient := 1, monomial := { powers := [0, 1, 0, 1], powers_length := _ } }] }
-/
#guard_msgs in
#eval ((Macaulean.Polynomial.mk (n := 4) [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [0,1,0,0]⟩]) *
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [0,0,1,0]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,0,0,1]⟩]))

/--
info: { terms := [{ coefficient := 2, monomial := { powers := [2, 0, 0, 0], powers_length := _ } },
            { coefficient := 2, monomial := { powers := [1, 1, 0, 0], powers_length := _ } },
            { coefficient := 3, monomial := { powers := [1, 0, 1, 0], powers_length := _ } },
            { coefficient := 3, monomial := { powers := [0, 1, 1, 0], powers_length := _ } },
            { coefficient := 1, monomial := { powers := [1, 0, 0, 1], powers_length := _ } },
            { coefficient := 1, monomial := { powers := [0, 1, 0, 1], powers_length := _ } }] }
-/
#guard_msgs in
#eval (((Macaulean.Polynomial.mk (n := 4) [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [0,1,0,0]⟩]) *
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [0,0,1,0]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,0,0,1]⟩])) +
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [0,1,0,0]⟩]) *
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,0,1,0]⟩]))

-- (2a + 2b) * (c + 1/2*d) + (2a + 2b) * (1a + 1/2c)
example : ((Macaulean.Polynomial.mk (n := 4) [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [0,1,0,0]⟩]) *
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [0,0,1,0]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,0,0,1]⟩])) +
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [0,1,0,0]⟩]) *
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨(1 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(1/2 : Rat), Macaulean.Mon.ofPowers [0,0,1,0]⟩])
       =
    (Macaulean.Polynomial.mk (n := 4) [
      ⟨2, .ofPowers [2,0,0,0]⟩,
      ⟨2, .ofPowers [1,1,0,0]⟩,
      ⟨3, .ofPowers [1,0,1,0]⟩,
      ⟨3, .ofPowers [0,1,1,0]⟩,
      ⟨1, .ofPowers [1,0,0,1]⟩,
      ⟨1, .ofPowers [0,1,0,1]⟩]) := by
  simp only [HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]
  simp +decide +arith [Macaulean.Polynomial.mul, Macaulean.Polynomial.add,
    Rat.mul_def', Rat.div_def, Int.sign, mkRat, Rat.add_def']
--  decide +kernel

example : (Macaulean.Polynomial.mk (n := 4) [
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [1,0,0,0]⟩,
      ⟨(2 : Rat), Macaulean.Mon.ofPowers [0,1,0,0]⟩])^2 =
      (.mk [
        ⟨4, .ofPowers [2,0,0,0]⟩,
        ⟨8, .ofPowers [1,1,0,0]⟩,
        ⟨4, .ofPowers [0,2,0,0]⟩]) := by
  simp only [HPow.hPow, Pow.pow, NatPow.pow]
  simp +decide +arith [Macaulean.Polynomial.pow,Macaulean.Polynomial.mul, Macaulean.Polynomial.add,
      Rat.mul_def', Rat.div_def, Int.sign, mkRat, Rat.add_def']

-- namespace BenchmarkExample

-- open Lean Macaulean

-- def n : Nat := 9
-- def u : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 0 (by simp [n])⟩]
-- def r : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 1 (by simp [n])⟩]
-- def k : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 2 (by simp [n])⟩]
-- def x : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 3 (by simp [n])⟩]
-- def y : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 4 (by simp [n])⟩]
-- def z : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 5 (by simp [n])⟩]
-- def a : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 6 (by simp [n])⟩]
-- def b : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 7 (by simp [n])⟩]
-- def c : Polynomial Rat n := .mk [⟨1,.fromVar <| .mk 8 (by simp [n])⟩]

-- -- variable (u' r' k' x' y' z' a' b' c' : Rat)

-- -- def ctx : Context Rat := RArray.ofArray #[u',r',k',x',y',z',a',b',c'] (by simp)

-- set_option maxHeartbeats 20000000

-- #check Macaulean.Polynomial.instOfNat

-- example
--   --(let ctx : Context Rat := RArray.ofArray #[u',r',k',x',y',z',a',b',c'] (by simp)
--   (ctx : Context Rat)
--   (ho : ((x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2).denote ctx = 0)
--   (hi : (a ^ 2 + b ^ 2 - c ^ 2).denote ctx = 0)
--   (hpq : (x * a + y * b - z * c).denote ctx = 0)
--   (hk : (k ^ 2 - (u + r) ^ 2 + (Macaulean.Polynomial.mk [⟨1,.unit⟩])).denote ctx = 0) :
--   ((r *
--             ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--               (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                       (r * (u + r) - 2) * k * a * c +
--                     (2 - (u + r) * (u + 2 * r)) * b * c -
--                   u * k * c ^ 2) *
--                 z) +
--           r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) ^
--         4 *
--       y ^ 2 -
--     r ^ 2 * 2 ^ 2 * k ^ 2 * z ^ 2 *
--       (r ^ 2 *
--             (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--                   (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                           (r * (u + r) - 2) * k * a * c +
--                         (2 - (u + r) * (u + 2 * r)) * b * c -
--                       u * k * c ^ 2) *
--                     z) ^
--                 3 *
--               (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z)) +
--           (1 - u ^ 2 - r ^ 2) *
--             (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--                   (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                           (r * (u + r) - 2) * k * a * c +
--                         (2 - (u + r) * (u + 2 * r)) * b * c -
--                       u * k * c ^ 2) *
--                     z) ^
--                 2 *
--               (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 2) +
--         u ^ 2 *
--             ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--               (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                       (r * (u + r) - 2) * k * a * c +
--                     (2 - (u + r) * (u + 2 * r)) * b * c -
--                   u * k * c ^ 2) *
--                 z) *
--           (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 3)).denote ctx = 0
--    := by
--     simp only [n, u,r,k,x,y,z,a,b,c,HMul.hMul, Mul.mul, HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, HPow.hPow, Pow.pow, NatPow.pow, Mon.fromVar, Mon.fromVarPower, Polynomial.pow, OfNat.ofNat] at *
--     simp at *
--     simp +decide +arith [Macaulean.Polynomial.pow,Macaulean.Polynomial.mul, Macaulean.Polynomial.add,
--       Macaulean.Polynomial.sub, Macaulean.Mon.mul, Macaulean.Mon.unit, Macaulean.Polynomial.neg,
--       Rat.mul_def', Rat.div_def, Int.sign, mkRat, Rat.add_def']

--     sorry

-- end BenchmarkExample
