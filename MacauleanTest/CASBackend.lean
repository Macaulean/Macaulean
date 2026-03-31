import Macaulean
import MRDI.CAS

open Lean Json
open Macaulean.CAS
open MRDI.CAS

namespace MacauleanTest.CASBackend

def requireIO (cond : Bool) (msg : String) : IO Unit :=
  unless cond do
    throw <| IO.userError msg

-- Test that backends and strategies are registered
#eval do
  let backends ← getRegisteredBackends
  requireIO (backends.any fun b => b.name == `Macaulay2)
    "Macaulay2 backend should be registered"

  let strategies ← getRegisteredStrategies
  requireIO (strategies.any fun s => s.name == `idealMembership)
    "idealMembership strategy should be registered"
  requireIO (strategies.any fun s => s.name == `reducibility)
    "reducibility strategy should be registered"

-- Test factorization via CAS backend
#eval do
  let ctx ← mkCASContext
  try
    let problem : FactorizationProblem := { n := 12 }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := FactorizationResult) response with
      | .ok (r : FactorizationResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO (result.factors.size > 0) "factorization should return factors"
    let mut product : Nat := 1
    for (p, e) in result.factors do
      product := product * p ^ e
    requireIO (product == 12) s!"factors of 12 should multiply to 12, got {product}"
  finally
    ctx.cleanup

-- Test reduction via CAS backend
#eval do
  let ctx ← mkCASContext
  try
    let ring : PolyRing := { coeff := .int, vars := #["x", "y"] }
    let elementData : MRDI.PolynomialData := #[
      ⟨1, #[⟨0, 3⟩]⟩,
      ⟨-1, #[⟨0, 1⟩, ⟨1, 1⟩]⟩
    ]
    let gen1Data : MRDI.PolynomialData := #[
      ⟨1, #[⟨0, 2⟩]⟩,
      ⟨-1, #[⟨1, 1⟩]⟩
    ]
    let gen2Data : MRDI.PolynomialData := #[
      ⟨1, #[⟨1, 2⟩]⟩
    ]
    let problem : ReductionProblem := {
      element := { ring, data := elementData }
      ideal := { ring, generators := #[gen1Data, gen2Data] }
      order := .grevlex
    }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := ReductionResult) response with
      | .ok (r : ReductionResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    let remainderPoly := Lean.Grind.CommRing.PolynomialData.deserialize result.remainder
    requireIO (remainderPoly == Lean.Grind.CommRing.Poly.num 0) "remainder should be zero for ideal member"
  finally
    ctx.cleanup

end MacauleanTest.CASBackend
