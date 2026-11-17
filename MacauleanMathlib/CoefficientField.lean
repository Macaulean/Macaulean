import Mathlib.Algebra.Ring.GrindInstances
import Macaulean.Algebra.CoefficientField

/-!
Mathlib structure on the already checked coefficient operations. This adapter is
restricted to the bridge's field carrier; it does not introduce a general reverse
instance from Grind's hierarchy into Mathlib's hierarchy.
-/
namespace Macaulean.Algebra

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

@[implicit_reducible]
instance (F : CoefficientField) : CommRing F.Carrier :=
  let s : Lean.Grind.CommRing F.Carrier := inferInstance
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one, Lean.Grind.Semiring.natCast_succ] }

end Macaulean.Algebra
