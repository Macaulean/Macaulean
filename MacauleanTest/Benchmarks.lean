import Lean
import Macaulean.IdealMembership
open Lean Grind Elab Tactic Meta

set_option maxHeartbeats 100000000
set_option maxRecDepth 202400
set_option pp.rawOnError true

--this theorem really should be proven elsewhere
private theorem RArray_get_ofArray (h : i < arr.size) : (RArray.ofArray arr len_hyp).get i = arr[i] := by
  have irw : i = ↑(Fin.mk i h) := by simp
  conv =>
    left
    right
    rw [irw]
  rw [RArray.ofArray, RArray.get_ofFn]
  simp

-- /- From https://github.com/leanprover/lean4/issues/11861 -/
-- theorem foo
--   (u r k x y z a b c : Rat)
--   (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
--   (hi : a ^ 2 + b ^ 2 - c ^ 2 = 0)
--   (hpq : x * a + y * b - z * c = 0)
--   (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
--   (r *
--             ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--               (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                       (r * (u + r) - 2) * k * a * c +
--                     (2 - (u + r) * (u + 2 * r)) * b * c -
--                   u * k * c ^ 2) *
--                 z) +
--           r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) ^
--         4 *
--       y ^ 2 -
--     r ^ 2 * 2 ^ 2 * k ^ 2 * z ^ 2 *
--       (r ^ 2 *
--             (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--                   (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                           (r * (u + r) - 2) * k * a * c +
--                         (2 - (u + r) * (u + 2 * r)) * b * c -
--                       u * k * c ^ 2) *
--                     z) ^
--                 3 *
--               (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z)) +
--           (1 - u ^ 2 - r ^ 2) *
--             (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--                   (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                           (r * (u + r) - 2) * k * a * c +
--                         (2 - (u + r) * (u + 2 * r)) * b * c -
--                       u * k * c ^ 2) *
--                     z) ^
--                 2 *
--               (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 2) +
--         u ^ 2 *
--             ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
--               (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
--                       (r * (u + r) - 2) * k * a * c +
--                     (2 - (u + r) * (u + 2 * r)) * b * c -
--                   u * k * c ^ 2) *
--                 z) *
--           (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 3) = 0 := by
--   m2idealmem -grind [ho, hi, hpq, hk]
--   clear ho hi hpq hk
--   -- simp [Macaulean.Polynomial.denote, Macaulean.Mon.denote, RArray_get_ofArray]
--   -- simp [*]
--   sorry


theorem foo3
  (u r k x y z a b c : Rat)
  (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
  (hi : a ^ 2 + b ^ 2 - c ^ 2 = 0)
  (hpq : x * a + y * b - z * c = 0)
  (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
    u^4*z^4-2*u^2*r^2*z^4+r^4*z^4-4*u^3*x*z^3+4*u*r^2*x*z^3+6*u^2*x^2*z^2-2*r^2*x^2*z^2+2*u^2*y^2*z^2-2*r^2*y^2*z^2-4*u*x^3*z-4*u*x*y^2*z+u^4+4*u^3*r+6*u^2*r^2+4*u*r^3+r^4-2*u^2*k^2-4*u*r*k^2-2*r^2*k^2+k^4+x^4+2*x^2*y^2+y^4+x^2*a^2+a^4+2*x*y*a*b+y^2*b^2+2*a^2*b^2+b^4-2*x*z*a*c-2*y*z*b*c+z^2*c^2-2*a^2*c^2-2*b^2*c^2+c^4-2*u^2-4*u*r-2*r^2+2*k^2+1 = 0 := by
    m2idealmem -grind [ho, hi, hpq, hk]
    grind

theorem foo2
  (u r k x y z : Rat)
  (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
  (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
    r^2*k^2*z^2-1/4*k^4*z^2-u*r^2*x*z-r^3*x*z+1/2*u*k^2*x*z+r*k^2*x*z-1/2*u*r*x^2-1/2*r^2*x^2-1/4*k^2*x^2-1/2*u*r*y^2-1/2*r^2*y^2-1/4*k^2*y^2+r^2*z^2-1/2*k^2*z^2+1/2*u*
      x*z+r*x*z-1/4*x^2-1/4*y^2-1/4*z^2 = 0 := by
  grind
