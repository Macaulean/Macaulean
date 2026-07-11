import Lean
import Macaulean.IdealMembership

theorem foo3
  (u r k x y z a b c : Rat)
  (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
  (hi : a ^ 2 + b ^ 2 - c ^ 2 = 0)
  (hpq : x * a + y * b - z * c = 0)
  (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
    u^4*z^4-2*u^2*r^2*z^4+r^4*z^4-4*u^3*x*z^3+4*u*r^2*x*z^3+6*u^2*x^2*z^2-2*r^2*x^2*z^2+2*u^2*y^2*z^2-2*r^2*y^2*z^2-4*u*x^3*z-4*u*x*y^2*z+u^4+4*u^3*r+6*u^2*r^2+4*u*r^3+r^4-2*u^2*k^2-4*u*r*k^2-2*r^2*k^2+k^4+x^4+2*x^2*y^2+y^4+x^2*a^2+a^4+2*x*y*a*b+y^2*b^2+2*a^2*b^2+b^4-2*x*z*a*c-2*y*z*b*c+z^2*c^2-2*a^2*c^2-2*b^2*c^2+c^4-2*u^2-4*u*r-2*r^2+2*k^2+1 = 0 := by
    m2idealmem -grind [ho, hi, hpq, hk]
    grind

-- set_option maxHeartbeats 10000000
-- theorem foo4
--   (u r k x y z a b c : Rat)
--   (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
--   (hi : a ^ 2 + b ^ 2 - c ^ 2 = 0)
--   (hpq : x * a + y * b - z * c = 0)
--   (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
--     u^2*k^4*z^4-2*u*r*k^4*z^4+r^2*k^4*z^4+4*u^2*r*k^2*x*z^3-4*r^3*k^2*x*z^3-4*u*k^4*x*z^3+4*r*k^4*x*z^3+4*u^2*r^2*x^2*z^2+8*u*r^3*x^2*z^2+4*r^4*x^2*z^2+2*u^2*k^2*x^2*z^2-8*u*r*k^2*x^2*z^2-10*r^2*k^2*x^2*z^2+4*k^4*x^2*z^2+2*u^2*k^2*y^2*z^2-2*r^2*k^2*y^2*z^2+2*u^2*k^2*z^4-4*u*r*k^2*z^4+2*r^2*k^2*z^4+4*u^2*r*x^3*z+8*u*r^2*x^3*z+4*r^3*x^3*z-4*u*k^2*x^3*z-4*r*k^2*x^3*z+4*u^2*r*x*
--     y^2*z+8*u*r^2*x*y^2*z+4*r^3*x*y^2*z-4*u*k^2*x*y^2*z-4*r*k^2*x*y^2*z+4*u^2*r*x*z^3-4*r^3*x*z^3-8*u*k^2*x*z^3+8*r*k^2*x*z^3+u^2*x^4+2*u*r*x^4+r^2*x^4+2*u^2*x^2*y^2+4*u*r*x^2*y^2+2*r^2*x^2*y^2+u^2*y^4+2*u*r*y^4+r^2*y^4+2*u^2*x^2*z^2-8*u*r*x^2*z^2-10*r^2*x^2*z^2+8*k^2*x^2*z^2+2*u^2*y^2*z^2-2*r^2*y^2*z^2+u^2*z^4-2*u*r*z^4+r^2*z^4-4*u*x^3*z-4*r*x^3*z-4*u*x*y^2*z-4*r*x*y^2*z-4*
--     u*x*z^3+4*r*x*z^3+4*x^2*z^2 = 0 := by
--   m2idealmem -grind [ho, hi, hpq, hk]
--   grind

example
  (u r k x y z a b c : Rat)
  (ho : (x - u * z) ^ 2 + y ^ 2 - r ^ 2 * z ^ 2 = 0)
  (hi : a ^ 2 + b ^ 2 - c ^ 2 = 0)
  (hpq : x * a + y * b - z * c = 0)
  (hk : k ^ 2 - (u + r) ^ 2 + 1 = 0) :
    (u*k^2*z^2-r*k^2*z^2+2*u*r*x*z+2*r^2*x*z-2*k^2*x*z+u*x^2+
    r*x^2+u*y^2+r*y^2+u*z^2-r*z^2-2*x*z)^2 = 0 := by
    m2idealmem -grind [ho, hi, hpq, hk]
    grind

--non-radical example
example
  {x y z : Rat}

  (f1 : x*y*z^2-z^3 = 0)
  (f2 : x*y^2*z-y*z^2 = 0)
  (f3 : x^2*y*z-x*z^2 = 0)
  (f4 : x*y^3-y^2*z = 0)
  (f5 : x^2*y^2-z^2 = 0)
  (f6 : x^3*y-x^2*z = 0) :
  y*x^3-y+1 = 0 := by
  m2remainder [f1, f2, f3, f4, f5, f6]

  sorry
