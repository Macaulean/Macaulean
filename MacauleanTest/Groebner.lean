import Macaulean

open Lean Grind

namespace MacauleanTest.Groebner

-- gb_reduce should handle the same ideal membership goals as cas
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  gb_reduce

example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x - y) [x * x - y, y * y] := by
  gb_reduce

-- cas tactic should also work (gb_reduce strategy is a fallback)
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.InIdeal (x * x * x - x * y) [x * x - y, y * y] := by
  cas

-- ============================================================================
-- Radical membership tests
-- ============================================================================

-- x ∈ √⟨x²⟩ because x² ∈ ⟨x²⟩
example {R : Type} [CommRing R] (x : R) :
    Macaulean.InRadical x [x * x] := by
  cas

-- x ∈ √⟨x³⟩ because x³ ∈ ⟨x³⟩
example {R : Type} [CommRing R] (x : R) :
    Macaulean.InRadical x [x * x * x] := by
  cas

-- ============================================================================
-- Polynomial divisibility tests — CAS finds the cofactor, kernel verifies
-- The user doesn't know the cofactor. cas figures it out.
-- ============================================================================

-- (x - y) divides (x^4 - y^4): cofactor is (x+y)(x^2+y^2)
-- Without cas, you'd have to guess/compute (x+y)(x^2+y^2) yourself
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.PolyDivides (x - y) (x ^ 4 - y ^ 4) := by
  cas

-- (x + y) divides (x^3 + y^3)
example {R : Type} [CommRing R] (x y : R) :
    Macaulean.PolyDivides (x + y) (x ^ 3 + y ^ 3) := by
  cas

-- (x - 1) divides (x^3 - 1)
example {R : Type} [CommRing R] (x : R) :
    Macaulean.PolyDivides (x - 1) (x ^ 3 - 1) := by
  cas

-- ============================================================================
-- Backend-level factorization tests (verify CAS computes correct factors)
-- ============================================================================

open Macaulean.CAS MRDI.CAS

def requireIO (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

-- Factor x^4 - y^4 via SymPy, verify product in CommRing.Poly arithmetic
#eval do
  let descs ← getRegisteredBackends
  let sympyDescs := descs.filter fun (b : CASBackendDesc) => b.name == `SymPy
  let backends ← sympyDescs.mapM fun d => LiveBackend.new d
  let cache ← IO.mkRef ({} : CASCache)
  let ctx : CASContext := { backends, cache }
  try
    let ring : PolyRing := { coeff := .int, vars := #["x", "y"] }
    let polyData : MRDI.PolynomialData := #[⟨1, #[⟨0, 4⟩]⟩, ⟨-1, #[⟨1, 4⟩]⟩]
    let problem : PolyFactorizationProblem := { ring, polynomial := polyData }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := PolyFactorizationResult) response with
      | .ok (r : PolyFactorizationResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO (result.factors.size == 3)
      s!"Expected 3 factors for x⁴-y⁴, got {result.factors.size}"
    let origPoly := Lean.Grind.CommRing.PolynomialData.deserialize polyData
    let factorPolys := result.factors.map Lean.Grind.CommRing.PolynomialData.deserialize
    let product := factorPolys.foldl (init := Lean.Grind.CommRing.Poly.num 1)
      fun acc p => Lean.Grind.CommRing.Poly.mul acc p
    requireIO (origPoly == product)
      "Product of factors should equal original polynomial"
  finally
    ctx.cleanup

end MacauleanTest.Groebner
