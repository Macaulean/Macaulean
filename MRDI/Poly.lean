import Lean.Data.Json.FromToJson.Extra
import MRDI.Basic

open Lean Json

namespace MRDI

instance : ToJson Grind.CommRing.Power where
  toJson p := .arr #[p.x, p.k]

instance : FromJson Grind.CommRing.Power where
  fromJson? := fun
    | .arr #[x, k] => do
      let xnat ← x.getNat?
      let knat ← k.getNat?
      pure ⟨xnat, knat⟩
    | _ => .error "Expected a pair of naturals"

/-- An array of powers representing a monomial. -/
def Monomial := Array Grind.CommRing.Power
deriving instance ToJson for Monomial
deriving instance FromJson for Monomial
deriving instance Repr for Monomial

/-- A term in a polynomial, consisting of a coefficient and a monomial. -/
structure Term where
  coeff : Int
  mon : Monomial
  deriving Repr

instance : ToJson Term where
  toJson t := .arr #[t.coeff, toJson t.mon]

instance : FromJson Term where
  fromJson? := fun
    | .arr #[c, m] => do
      let cnat ← c.getNat?
      let mon ← fromJson? m
      pure ⟨cnat, mon⟩
    | _ => .error "Expected a pair of a coefficient and a monomial"

/-- A polynomial represented as an array of terms. -/
def PolynomialData := Array Term
deriving instance ToJson for PolynomialData
deriving instance FromJson for PolynomialData
deriving instance Repr for PolynomialData

structure Poly where
  data : PolynomialData
  deriving Repr

instance : ToJson Poly where
  toJson p := toJson p.data

instance : FromJson Poly where
  fromJson? x := do
    let pdata ← fromJson? x
    pure <| Poly.mk pdata


def polyToTermList : Grind.CommRing.Poly → List Term := fun
  | .num k => [{coeff := k, mon := #[]}]
  | .add k v p => {coeff := k, mon := (monToPowerList v).toArray} :: polyToTermList p
  where
    monToPowerList : Grind.CommRing.Mon → List Grind.CommRing.Power := fun
      | .unit => []
      | .mult p m => p :: monToPowerList m

def polyFromTermArray (terms : Array Term) : Grind.CommRing.Poly :=
  if h : terms.size <= 0 -- this instead of isEmpty to make dealing with a proof easier
  then .num 0
  else
    let lastTerm :=
      let t := terms.back (Nat.lt_of_not_le h)
      if t.mon.isEmpty
      then .num t.coeff
      else .add t.coeff (powerArrayToMon t.mon) <| .num 0
    terms.foldr (start := terms.size - 1)
      (fun t p => .add t.coeff (powerArrayToMon t.mon) p) <| lastTerm
  where
    powerArrayToMon (powers : Array Grind.CommRing.Power) : Grind.CommRing.Mon :=
      powers.foldr (.mult) .unit

deriving instance TypeName for Grind.CommRing.Poly

instance : MrdiType Grind.CommRing.Poly where
  mrdiType := .string "Lean.Grind.CommRing.Poly"
  decode? json := (polyFromTermArray <$> ·) <$> trivialDecode? json
  encode p := trivialEncode ({data := (polyToTermList p).toArray} : Poly)
