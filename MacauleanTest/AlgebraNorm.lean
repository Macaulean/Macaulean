/-
  Tests for `algebra_norm_reflect` / `algebra_norm`.

  Every theorem here must be sorry-free and use only the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) -- in particular never
  `Lean.ofReduceBool`, i.e. never `native_decide`.
-/
import Macaulean.Grind.AlgPoly.Tactic

namespace MacauleanTest.AlgebraNorm

set_option maxRecDepth 100000

theorem sq_add (x y : Rat) : (x + y) ^ 2 = x * x + 2 * (x * y) + y * y := by
  algebra_norm_reflect

theorem diff_of_squares (x y : Int) : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by
  algebra_norm_reflect

theorem cube_binomial (x y : Rat) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  algebra_norm_reflect

theorem collect_like (x : Rat) : 3 * x + 4 * x = 7 * x := by
  algebra_norm_reflect

theorem negation (x y : Rat) : -(x - y) = y - x := by
  algebra_norm_reflect

/-- Atoms need not be variables: anything the reifier does not recognise as
arithmetic becomes an atom. -/
theorem opaque_atoms (f : Rat → Rat) (x : Rat) :
    (f x + 1) * (f x - 1) = f x ^ 2 - 1 := by
  algebra_norm_reflect

/-- A certificate-shaped identity: `A * B = Q * G + R`. -/
theorem certificate_shape (x y z : Rat) :
    (x ^ 2 + y) * (x - z) =
      (x + y) * (x ^ 2 - x * z) + (x * y - y * z - x ^ 2 * y + x * y * z) := by
  algebra_norm_reflect

/-- `algebra_norm` falls back on `grind`, so it can use hypotheses. -/
theorem uses_hypothesis (x y : Rat) (h : x = y) : x * x = y * y := by
  algebra_norm

#print axioms sq_add
#print axioms cube_binomial
#print axioms certificate_shape
#print axioms uses_hypothesis

end MacauleanTest.AlgebraNorm
