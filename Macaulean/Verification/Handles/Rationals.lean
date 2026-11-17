import Macaulean.Verification.Handles.Simp

/-! Rational representation. Arithmetic dispatch is handled generically by
`Operators.lean`, using the production evaluator rather than per-type lemmas. -/
namespace Macaulean.M2.Handles

@[m2_simp] theorem toValue_rat (q : Rat) : ToM2.toValue q = Value.qq q := rfl

end Macaulean.M2.Handles
