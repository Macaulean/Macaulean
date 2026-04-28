/-
  New polynomial representation for Macaulean.

  Polynomials as sorted lists of coefficient-monomial pairs, using
  Grind.CommRing.Mon for monomials in strictly decreasing grevlex order.
-/
import Lean
import Macaulean.Polynomial.Basic
import Macaulean.Polynomial.Lemmas
open Lean Grind CommRing

namespace Macaulean



-- theorem denote_mul [CommRing R] (ctx : Context R)

namespace Polynomial


/-! ## Denotation theorems -/

section Theorems
variable {R : Type} [inst : Grind.CommRing R] [deceq : DecidableEq R] [leq : LawfulBEq R]
open Grind.Semiring Grind.Ring Grind.CommSemiring
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast





end Theorems

/-! ## fromGrindPoly correctness -/

section FromGrindCorrectness
variable {R : Type} [inst : Grind.CommRing R]
attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast
open Grind.Semiring Grind.Ring

--TODO reconsider the theorems in this section

-- private theorem fromGrindPoly_go_append (p : CommRing.Poly) (acc : List (PolyTerm Int (numVars p))) :
--     fromGrindPoly.go p acc = acc ++ fromGrindPoly.go p [] := by
--   induction p generalizing acc with
--   | num k => simp only [fromGrindPoly.go]; split <;> simp
--   | add k m p ih =>
--     simp only [fromGrindPoly.go]; split
--     · exact ih acc
--     · simp only [List.nil_append]; rw [ih (acc ++ _), ih [⟨k, m⟩]]; simp

-- attribute [local instance] Grind.Ring.zsmul

-- private theorem fromGrindPoly_go_denote (ctx : Context R) (p : CommRing.Poly)
--     (acc : List (PolyTerm Int (numVars p))) :
--     denoteTerms ctx ((fromGrindPoly.go p acc).map fun t => ⟨Int.cast t.coefficient, t.monomial⟩) =
--     denoteTerms ctx (acc.map fun t => ⟨Int.cast t.coefficient, t.monomial⟩) + p.denote ctx := by
--   induction p with
--   | num k =>
--     simp only [fromGrindPoly.go]
--     split
--     · next h =>
--       simp at h
--       subst h
--       unfold Poly.denote
--       rw [intCast_zero, add_zero]
--     · unfold Poly.denote
--       simp only [List.map_append, List.map_cons, List.map_nil, denoteTerms_append, denoteTerms,
--         Mon.denote, mul_one, add_zero]
--   | add k m p ih =>
--     simp only [fromGrindPoly.go]
--     split
--     · next h =>
--       simp at h
--       subst h
--       rw [ih]
--       congr 1
--       unfold Poly.denote
--       rw [zsmul_eq_intCast_mul, intCast_zero, zero_mul, add_comm (0 : R), add_zero]
--       cases p with
--       | num _ => rfl
--       | add _ _ _ => rfl
--     · rw [ih]
--       simp only [List.map_append, List.map_cons, List.map_nil, denoteTerms_append, denoteTerms,
--         add_zero]
--       have hd : ∀ (q : Poly), Poly.denote ctx q =
--           match q with
--           | .num k => ↑k
--           | .add k m q => k • Mon.denote ctx m + Poly.denote ctx q := by
--         intro q; cases q with | num _ => rfl | add _ _ _ => rfl
--       rw [hd (.add k m p)]
--       simp only [zsmul_eq_intCast_mul, add_assoc]

-- theorem denote_fromGrindPolyAs (ctx : Context R) (p : CommRing.Poly) :
--     denote ctx (fromGrindPolyAs p) = p.denote ctx := by
--   simp only [fromGrindPolyAs, fromGrindPoly, denote]
--   rw [fromGrindPoly_go_denote ctx p []]
--   simp [zero_add']

end FromGrindCorrectness


end Polynomial
end Macaulean
