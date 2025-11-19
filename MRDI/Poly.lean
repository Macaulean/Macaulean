import Lean.Data.Json.FromToJson.Extra

open Lean Json

def Lean.githubURL := "https://github.com/leanprover/lean4"

namespace MRDI

instance : ToJson Grind.CommRing.Power where
  toJson p := .arr #[p.x, p.k]

/-- An array of powers representing a monomial. -/
def Monomial := Array Grind.CommRing.Power
deriving instance ToJson for Monomial

/-- A term in a polynomial, consisting of a coefficient and a monomial. -/
structure Term where
  coeff : Int
  mon : Monomial

instance : ToJson Term where
  toJson t := .arr #[t.coeff, toJson t.mon]

/-- A polynomial represented as a list of terms. -/
def PolynomialData := Array Term
deriving instance ToJson for PolynomialData

structure Poly where
  version : String := Lean.versionString
  data : PolynomialData

instance : ToJson Poly where
  toJson p := .mkObj [("_ns", .mkObj [("Lean", .arr #[.str Lean.githubURL, .str
  p.version])]), ("_type", .str "Lean.Grind.CommRing.Poly"), ("data", toJson p.data)]

-- def test : Poly := {
--   data := #[
--     { coeff := 3, mon := #[] },
--     { coeff := 5, mon := #[ ⟨2, 3⟩ ] }
--   ]
-- }
-- #eval toJson test
