import Macaulean

open Lean.Grind.CommRing

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
