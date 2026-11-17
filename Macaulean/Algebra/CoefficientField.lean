import Macaulean.Algebra.PrimeField
import Init.GrindInstances.Ring.Rat

/-! The two coefficient-field families supported by the mathematical bridge. -/
namespace Macaulean.Algebra

inductive CoefficientField where
  | rationals
  | prime (field : PrimeField.Checked)

def CoefficientField.Carrier : CoefficientField → Type
  | .rationals => Rat
  | .prime F => F.Carrier

instance (F : CoefficientField) : Lean.Grind.Field F.Carrier := by
  cases F with
  | rationals => exact inferInstanceAs (Lean.Grind.Field Rat)
  | prime F => exact inferInstanceAs (Lean.Grind.Field F.Carrier)

instance (F : CoefficientField) : DecidableEq F.Carrier := by
  cases F with
  | rationals => exact inferInstanceAs (DecidableEq Rat)
  | prime F => exact inferInstanceAs (DecidableEq F.Carrier)

/-- The characteristic is part of the coefficient field, not a printer setting. -/
def CoefficientField.characteristic : CoefficientField → Nat
  | .rationals => 0
  | .prime F => F.characteristic

end Macaulean.Algebra
