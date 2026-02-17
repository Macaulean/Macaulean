import Lean
import Macaulean.IdealMembership
open Lean Grind Elab Tactic Meta

set_option maxHeartbeats 10000000

/- From https://github.com/leanprover/lean4/issues/11861 -/
theorem foo
  (u r k x y z a b c : Rat)
  (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
  (hi : a ^ 2 + b ^ 2 - c ^ 2 = 0)
  (hpq : x * a + y * b - z * c = 0)
  (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
  (r *
            ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
              (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                      (r * (u + r) - 2) * k * a * c +
                    (2 - (u + r) * (u + 2 * r)) * b * c -
                  u * k * c ^ 2) *
                z) +
          r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) ^
        4 *
      y ^ 2 -
    r ^ 2 * 2 ^ 2 * k ^ 2 * z ^ 2 *
      (r ^ 2 *
            (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) ^
                3 *
              (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z)) +
          (1 - u ^ 2 - r ^ 2) *
            (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) ^
                2 *
              (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 2) +
        u ^ 2 *
            ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
              (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                      (r * (u + r) - 2) * k * a * c +
                    (2 - (u + r) * (u + 2 * r)) * b * c -
                  u * k * c ^ 2) *
                z) *
          (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 3) = 0 := by
  -- m2idealmem [ho, hi, hpq, hk]
  sorry
