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

-- instance : ToJson Poly where
--   toJson p := .mkObj [("_ns", .mkObj [("Lean", .arr #[.str Lean.githubURL,
--                                                .str Lean.versionString])]),
--                       ("_type", .str "Lean.Grind.CommRing.Poly"),
--                       ("data", toJson p.data)]

instance : ToJson Poly where
  toJson p := toJson p.data

instance : FromJson Poly where
  fromJson? x := do
    let pdata ← fromJson? x
    pure <| Poly.mk pdata

instance : MrdiType Poly where
  mrdiType := .string "Lean.Grind.CommRing.Poly"
  decode? := trivialDecode?

def test : Poly := {
  data := #[
    { coeff := 3, mon := #[] },
    { coeff := 5, mon := #[ ⟨2, 3⟩ ] }
  ]
}
#eval toJson <| toMrdi test

#eval ((fromJson? <| toJson <| toMrdi test) >>= fromMrdi? (α := Poly))
