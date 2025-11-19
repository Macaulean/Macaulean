import Lean
open Lean Grind
open CommRing
#where
#check Poly

structure VarPower where
  var: Var
  exponent: Nat
  deriving Repr

#check VarPower.mk 3 5
#check (⟨3,7⟩:VarPower)
def vp1 : VarPower := { var := 3, exponent := 8}
#check vp1
#print vp1
#reduce vp1
#eval vp1

structure M2Monomial where
  monomial: List VarPower
  deriving Repr

structure M2Term where
  coefficient: Int
  term: M2Monomial
  deriving Repr

structure M2Poly where
  data: List M2Term
  deriving Repr

def serializePower (p : Power) : VarPower := ⟨p.x, p.k⟩
#check serializePower
#eval serializePower ⟨5, 7⟩

def serializeMonomial : Mon → M2Monomial
  | .unit =>  ⟨[]⟩
  | .mult p m => ⟨ serializePower p :: (serializeMonomial m).monomial ⟩

def serializePoly : Poly → M2Poly
  | .num k =>  ⟨[⟨k, serializeMonomial .unit⟩]⟩
  | .add k m p => ⟨ ⟨k, serializeMonomial m⟩:: (serializePoly p).data⟩

def a : Poly := .num 7
#eval a
#eval (serializePoly a)
