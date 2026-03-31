import Macaulean
import MRDI.CAS

open Lean Json
open Macaulean.CAS
open MRDI.CAS

namespace MacauleanTest.SymPyBackend

def requireIO (cond : Bool) (msg : String) : IO Unit :=
  unless cond do
    throw <| IO.userError msg

def isSympyDesc (b : CASBackendDesc) : Bool := b.name == `SymPy

-- Test that SymPy backend is registered alongside M2
#eval do
  let backends ← getRegisteredBackends
  requireIO (backends.any isSympyDesc) "SymPy backend should be registered"
  requireIO (backends.any fun (b : CASBackendDesc) => b.name == `Macaulay2)
    "Macaulay2 backend should still be registered"

-- Helper: create a CAS context with only the SymPy backend
def mkSymPyContext : IO CASContext := do
  let descs ← getRegisteredBackends
  let sympyDescs := descs.filter isSympyDesc
  let backends ← sympyDescs.mapM fun d => LiveBackend.new d
  let cache ← IO.mkRef ({} : CASCache)
  pure { backends, cache }

-- Test factorization via SymPy
#eval do
  let ctx ← mkSymPyContext
  try
    let problem : FactorizationProblem := { n := 60 }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := FactorizationResult) response with
      | .ok (r : FactorizationResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO (result.factors.size > 0) "SymPy should return factors"
    let mut product : Nat := 1
    for (p, e) in result.factors do
      product := product * p ^ e
    requireIO (product == 60) s!"SymPy factors of 60 should multiply to 60, got {product}"
  finally
    ctx.cleanup

-- Test polynomial reduction via SymPy
#eval do
  let ctx ← mkSymPyContext
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
    requireIO (remainderPoly == Lean.Grind.CommRing.Poly.num 0)
      "SymPy remainder should be zero for ideal member"
  finally
    ctx.cleanup

-- Test Gröbner basis computation via SymPy
#eval do
  let ctx ← mkSymPyContext
  try
    let ring : PolyRing := { coeff := .int, vars := #["x", "y"] }
    let gen1Data : MRDI.PolynomialData := #[
      ⟨1, #[⟨0, 2⟩]⟩,
      ⟨-1, #[⟨1, 1⟩]⟩
    ]
    let gen2Data : MRDI.PolynomialData := #[
      ⟨1, #[⟨1, 2⟩]⟩
    ]
    let problem : GroebnerBasisProblem := {
      ring
      generators := #[gen1Data, gen2Data]
      order := .grevlex
    }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := GroebnerBasisResult) response with
      | .ok (r : GroebnerBasisResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO (result.generators.size > 0) "SymPy should return a Gröbner basis"
  finally
    ctx.cleanup

end MacauleanTest.SymPyBackend
