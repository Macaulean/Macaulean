/-
Verification tests for the GMP-free (residue-vector / single-pass CRT) path of
`algebra_norm_reflect`.

Every theorem here is closed by `AlgExpr.eq_of_checkModZero`, whose kernel
evaluation stays inside Lean's boxed-scalar range; see the audit in
`Macaulean/Grind/AlgPoly/KroneckerMod.lean`.  Each `#print axioms` must show
only `propext, Classical.choice, Quot.sound` — in particular no `sorryAx` and
no `Lean.ofReduceBool` (the tactic never uses `native_decide`).
-/

import Macaulean.Grind.AlgPoly.Tactic

open Lean Grind

set_option linter.unusedVariables false

/-! ### Over `Int` -/

theorem mod_int_sq (x y : Int) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  algebra_norm_reflect

#print axioms mod_int_sq

theorem mod_int_big (x y : Int) :
    (1234567891 * x - 987654321 * y) * (1234567891 * x + 987654321 * y) =
      1524157877488187881 * x ^ 2 - 975461057789971041 * y ^ 2 := by
  algebra_norm_reflect

#print axioms mod_int_big

theorem mod_int_cube (x y z : Int) :
    (x + y + z) ^ 3 =
      x ^ 3 + y ^ 3 + z ^ 3
        + 3 * (x ^ 2 * y + x ^ 2 * z + y ^ 2 * x + y ^ 2 * z + z ^ 2 * x + z ^ 2 * y)
        + 6 * x * y * z := by
  algebra_norm_reflect

#print axioms mod_int_cube

/-! ### Over `Rat` -/

theorem mod_rat_sq (x y : Rat) :
    (3 * x - 5 * y) ^ 2 = 9 * x ^ 2 - 30 * x * y + 25 * y ^ 2 := by
  algebra_norm_reflect

#print axioms mod_rat_sq

/-! ### Over an arbitrary grind commutative ring -/

theorem mod_generic {α : Type} [CommRing α] (x y : α) :
    (x + y) ^ 4 =
      x ^ 4 + 4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + y ^ 4 := by
  algebra_norm_reflect

#print axioms mod_generic

theorem mod_generic_negatives {α : Type} [CommRing α] (a b c : α) :
    (a - b) * (b - c) * (c - a) =
      a * b * c - a * b * c
        + (-(a ^ 2 * b) + a ^ 2 * c + a * b ^ 2 - a * c ^ 2 - b ^ 2 * c + b * c ^ 2) := by
  algebra_norm_reflect

#print axioms mod_generic_negatives

/-! ### The exact-integer path is still available -/

set_option macaulean.gmpFree false in
theorem gmp_path_still_works {α : Type} [CommRing α] (x y : α) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  algebra_norm_reflect

#print axioms gmp_path_still_works

/-! ### A false identity is refused -/

example (x y : Int) : True := by
  fail_if_success
    have : (x + y) ^ 2 = x ^ 2 + 3 * x * y + y ^ 2 := by algebra_norm_reflect
  trivial

-- The error message reported for the goal above is the tactic's own:
--
--   algebra_norm_reflect could not solve the goal
--   direct attempt: GMP-free certificate failed: residue-vector normal forms
--   differ (base 4, 2 variables, 2 moduli)
--   exact-integer certificate failed: ...
