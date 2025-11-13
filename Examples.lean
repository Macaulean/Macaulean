import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Data.Json.FromToJson.Basic

open Lean Grind.CommRing

deriving instance ToJson for Lean.Grind.CommRing.Power
deriving instance FromJson for Lean.Grind.CommRing.Power
deriving instance ToJson for Lean.Grind.CommRing.Mon
deriving instance FromJson for Lean.Grind.CommRing.Mon
deriving instance ToJson for Lean.Grind.CommRing.Poly
deriving instance FromJson for Lean.Grind.CommRing.Poly

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
instance {n} : OfNat Expr n where
  ofNat := .num n

-- This is the wrong JSON representation for the polynomial

/--
info: {"add":
 {"v": {"mult": {"p": {"x": 3, "k": 5}, "m": "unit"}},
  "p":
  {"add":
   {"v":
    {"mult":
     {"p": {"x": 0, "k": 1},
      "m": {"mult": {"p": {"x": 2, "k": 2}, "m": "unit"}}}},
    "p":
    {"add":
     {"v": {"mult": {"p": {"x": 1, "k": 1}, "m": "unit"}},
      "p": {"num": {"k": 1}},
      "k": -1}},
    "k": 1}},
  "k": 1}}
-/
#guard_msgs in
#eval toJson (z^5 + w*y^2 - x + 1 |>.toPoly)
