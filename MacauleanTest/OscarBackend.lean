import Macaulean
import MRDI.CAS

open Lean Json
open Macaulean.CAS
open MRDI.CAS

namespace MacauleanTest.OscarBackend

def requireIO (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def isOscarDesc (b : CASBackendDesc) : Bool := b.name == `Oscar

-- Test that Oscar backend is registered alongside M2 and SymPy
#eval do
  let backends ← getRegisteredBackends
  requireIO (backends.any isOscarDesc) "Oscar backend should be registered"
  requireIO (backends.any fun (b : CASBackendDesc) => b.name == `Macaulay2) "M2 should be registered"
  requireIO (backends.any fun (b : CASBackendDesc) => b.name == `SymPy) "SymPy should be registered"

-- Helper: create a CAS context with only the Oscar backend
def mkOscarContext : IO CASContext := do
  let descs ← getRegisteredBackends
  let oscarDescs := descs.filter isOscarDesc
  let backends ← oscarDescs.mapM fun d => LiveBackend.new d
  let cache ← IO.mkRef ({} : CASCache)
  pure { backends, cache }

-- Factor x^4 - y^4 via Oscar
#eval do
  let ctx ← mkOscarContext
  try
    let ring : PolyRing := { coeff := .int, vars := #["x", "y"] }
    let polyData : MRDI.PolynomialData := #[⟨1, #[⟨0, 4⟩]⟩, ⟨-1, #[⟨1, 4⟩]⟩]
    let problem : PolyFactorizationProblem := { ring, polynomial := polyData }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := PolyFactorizationResult) response with
      | .ok (r : PolyFactorizationResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO (result.factors.size == 3)
      s!"Oscar: expected 3 factors for x⁴-y⁴, got {result.factors.size}"
    let origPoly := Lean.Grind.CommRing.PolynomialData.deserialize polyData
    let factorPolys := result.factors.map Lean.Grind.CommRing.PolynomialData.deserialize
    let product := factorPolys.foldl (init := Lean.Grind.CommRing.Poly.num 1)
      fun acc p => Lean.Grind.CommRing.Poly.mul acc p
    requireIO (origPoly == product)
      "Oscar: product of factors should equal original polynomial"
  finally
    ctx.cleanup

-- Test integer factorization via Oscar
#eval do
  let ctx ← mkOscarContext
  try
    let problem : FactorizationProblem := { n := 120 }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := FactorizationResult) response with
      | .ok (r : FactorizationResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    let mut product : Nat := 1
    for (p, e) in result.factors do
      product := product * p ^ e
    requireIO (product == 120) s!"Oscar: factors of 120 should multiply to 120, got {product}"
  finally
    ctx.cleanup

-- Test Gröbner basis via Oscar
#eval do
  let ctx ← mkOscarContext
  try
    let ring : PolyRing := { coeff := .int, vars := #["x", "y"] }
    let gen1 : MRDI.PolynomialData := #[⟨1, #[⟨0, 2⟩]⟩, ⟨-1, #[⟨1, 1⟩]⟩]
    let gen2 : MRDI.PolynomialData := #[⟨1, #[⟨1, 2⟩]⟩]
    let problem : GroebnerBasisProblem := { ring, generators := #[gen1, gen2], order := .grevlex }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := GroebnerBasisResult) response with
      | .ok (r : GroebnerBasisResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO (result.generators.size > 0) "Oscar should return a Gröbner basis"
  finally
    ctx.cleanup

end MacauleanTest.OscarBackend
