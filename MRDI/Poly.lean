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

deriving instance BEq for Grind.CommRing.Power
deriving instance DecidableEq for Grind.CommRing.Power

/-- An array of powers representing a monomial. -/
def Monomial := Array Grind.CommRing.Power
deriving instance ToJson for Monomial
deriving instance FromJson for Monomial
deriving instance Repr for Monomial
deriving instance BEq for Monomial
deriving instance DecidableEq for Monomial

/-- A term in a polynomial, consisting of a coefficient and a monomial. -/
structure Term where
  coeff : Int
  mon : Monomial
  deriving Repr, BEq, DecidableEq

instance : ToJson Term where
  toJson t := .arr #[t.coeff, toJson t.mon]

instance : FromJson Term where
  fromJson? := fun
    | .arr #[c, m] => do
      let cint ← c.getInt?
      let mon ← fromJson? m
      pure ⟨cint, mon⟩
    | _ => .error "Expected a pair of a coefficient and a monomial"

/-- A polynomial represented as an array of terms. -/
def PolynomialData := Array Term
deriving instance ToJson for PolynomialData
deriving instance FromJson for PolynomialData
deriving instance Repr for PolynomialData
deriving instance BEq for PolynomialData
deriving instance DecidableEq for PolynomialData

structure Poly where
  data : PolynomialData
  deriving Repr, BEq, DecidableEq

structure Ideal where
  numVars : Nat
  generators : Array PolynomialData
  deriving Repr, BEq, DecidableEq

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

instance : ToJson Ideal where
  toJson i := .mkObj [
    ("numVars", toJson i.numVars),
    ("generators", toJson i.generators)
  ]

instance : FromJson Ideal where
  fromJson? := fun
    | .obj entries => do
      let numVars ← fromJson? <| entries.getD "numVars" (.num 0)
      let generators ← fromJson? <| entries.getD "generators" (.arr #[])
      pure { numVars, generators }
    | _ => .error "Expected an ideal object"

instance : MrdiType Poly where
  mrdiType := .string "Lean.Grind.CommRing.Poly"
  decode? := trivialDecode? (.string "Lean.Grind.CommRing.Poly")

instance : MrdiType Ideal where
  mrdiType := .string "Lean.Grind.CommRing.Ideal"
  decode? := trivialDecode? (.string "Lean.Grind.CommRing.Ideal")

def test : Poly := {
  data := #[
    { coeff := 3, mon := #[] },
    { coeff := 5, mon := #[ ⟨2, 3⟩ ] }
  ]
}
