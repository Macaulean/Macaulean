import Macaulean.Verification.Handles.Simp

/-!
# Rational operations for handle proofs

The simplifier follows the production operator dispatch, including mixed ZZ/QQ
arguments. `/` requires a nonzero denominator; `//` and `%` retain their runtime
zero-divisor conventions. No field identities are assumed about runtime values.
-/
namespace Macaulean.M2.Handles

@[m2_simp] theorem toValue_rat (q : Rat) : ToM2.toValue q = Value.qq q := rfl

@[m2_simp] theorem qq_add (p : Rat) (q : Rat) :
    evalBinOp .add (.qq p) (.qq q) = .ok (.qq (p + q)) := rfl

@[m2_simp] theorem qq_sub (p : Rat) (q : Rat) :
    evalBinOp .sub (.qq p) (.qq q) = .ok (.qq (p - q)) := rfl

@[m2_simp] theorem qq_mul (p : Rat) (q : Rat) :
    evalBinOp .mul (.qq p) (.qq q) = .ok (.qq (p * q)) := rfl

@[m2_simp] theorem qq_eq (p : Rat) (q : Rat) :
    evalBinOp .eq (.qq p) (.qq q) = .ok (.bool (decide (p = q))) := rfl

@[m2_simp] theorem qq_ne (p : Rat) (q : Rat) :
    evalBinOp .ne (.qq p) (.qq q) = .ok (.bool (decide (p ≠ q))) := rfl

@[m2_simp] theorem qq_lt (p : Rat) (q : Rat) :
    evalBinOp .lt (.qq p) (.qq q) = .ok (.bool (decide (p < q))) := rfl

@[m2_simp] theorem qq_le (p : Rat) (q : Rat) :
    evalBinOp .le (.qq p) (.qq q) = .ok (.bool (decide (p ≤ q))) := rfl

@[m2_simp] theorem qq_gt (p : Rat) (q : Rat) :
    evalBinOp .gt (.qq p) (.qq q) = .ok (.bool (decide (p > q))) := rfl

@[m2_simp] theorem qq_ge (p : Rat) (q : Rat) :
    evalBinOp .ge (.qq p) (.qq q) = .ok (.bool (decide (p ≥ q))) := rfl

@[m2_simp] theorem qq_div (p : Rat) (q : Rat) :
    evalBinOp .div (.qq p) (.qq q) =
      (if q = 0 then .error .divByZero else .ok (.qq (p / q))) := rfl

@[m2_simp] theorem qq_zz_add (p : Rat) (q : Int) :
    evalBinOp .add (.qq p) (.zz q) = .ok (.qq (p + (q : Rat))) := rfl

@[m2_simp] theorem qq_zz_sub (p : Rat) (q : Int) :
    evalBinOp .sub (.qq p) (.zz q) = .ok (.qq (p - (q : Rat))) := rfl

@[m2_simp] theorem qq_zz_mul (p : Rat) (q : Int) :
    evalBinOp .mul (.qq p) (.zz q) = .ok (.qq (p * (q : Rat))) := rfl

@[m2_simp] theorem qq_zz_eq (p : Rat) (q : Int) :
    evalBinOp .eq (.qq p) (.zz q) = .ok (.bool (decide (p = (q : Rat)))) := rfl

@[m2_simp] theorem qq_zz_ne (p : Rat) (q : Int) :
    evalBinOp .ne (.qq p) (.zz q) = .ok (.bool (decide (p ≠ (q : Rat)))) := rfl

@[m2_simp] theorem qq_zz_lt (p : Rat) (q : Int) :
    evalBinOp .lt (.qq p) (.zz q) = .ok (.bool (decide (p < (q : Rat)))) := rfl

@[m2_simp] theorem qq_zz_le (p : Rat) (q : Int) :
    evalBinOp .le (.qq p) (.zz q) = .ok (.bool (decide (p ≤ (q : Rat)))) := rfl

@[m2_simp] theorem qq_zz_gt (p : Rat) (q : Int) :
    evalBinOp .gt (.qq p) (.zz q) = .ok (.bool (decide (p > (q : Rat)))) := rfl

@[m2_simp] theorem qq_zz_ge (p : Rat) (q : Int) :
    evalBinOp .ge (.qq p) (.zz q) = .ok (.bool (decide (p ≥ (q : Rat)))) := rfl

@[m2_simp] theorem qq_zz_div (p : Rat) (q : Int) :
    evalBinOp .div (.qq p) (.zz q) =
      (if (q : Rat) = 0 then .error .divByZero else .ok (.qq (p / (q : Rat)))) := rfl

@[m2_simp] theorem zz_qq_add (p : Int) (q : Rat) :
    evalBinOp .add (.zz p) (.qq q) = .ok (.qq ((p : Rat) + q)) := rfl

@[m2_simp] theorem zz_qq_sub (p : Int) (q : Rat) :
    evalBinOp .sub (.zz p) (.qq q) = .ok (.qq ((p : Rat) - q)) := rfl

@[m2_simp] theorem zz_qq_mul (p : Int) (q : Rat) :
    evalBinOp .mul (.zz p) (.qq q) = .ok (.qq ((p : Rat) * q)) := rfl

@[m2_simp] theorem zz_qq_eq (p : Int) (q : Rat) :
    evalBinOp .eq (.zz p) (.qq q) = .ok (.bool (decide ((p : Rat) = q))) := rfl

@[m2_simp] theorem zz_qq_ne (p : Int) (q : Rat) :
    evalBinOp .ne (.zz p) (.qq q) = .ok (.bool (decide ((p : Rat) ≠ q))) := rfl

@[m2_simp] theorem zz_qq_lt (p : Int) (q : Rat) :
    evalBinOp .lt (.zz p) (.qq q) = .ok (.bool (decide ((p : Rat) < q))) := rfl

@[m2_simp] theorem zz_qq_le (p : Int) (q : Rat) :
    evalBinOp .le (.zz p) (.qq q) = .ok (.bool (decide ((p : Rat) ≤ q))) := rfl

@[m2_simp] theorem zz_qq_gt (p : Int) (q : Rat) :
    evalBinOp .gt (.zz p) (.qq q) = .ok (.bool (decide ((p : Rat) > q))) := rfl

@[m2_simp] theorem zz_qq_ge (p : Int) (q : Rat) :
    evalBinOp .ge (.zz p) (.qq q) = .ok (.bool (decide ((p : Rat) ≥ q))) := rfl

@[m2_simp] theorem zz_qq_div (p : Int) (q : Rat) :
    evalBinOp .div (.zz p) (.qq q) =
      (if q = 0 then .error .divByZero else .ok (.qq ((p : Rat) / q))) := rfl

@[m2_simp] theorem zz_div (p q : Int) :
    evalBinOp .div (.zz p) (.zz q) =
      (if (q : Rat) = 0 then .error .divByZero else .ok (.qq ((p : Rat) / q))) := rfl

@[m2_simp] theorem qq_neg (q : Rat) : evalUnOp .neg (.qq q) = .ok (.qq (-q)) := rfl
@[m2_simp] theorem qq_pos (q : Rat) : evalUnOp .pos (.qq q) = .ok (.qq q) := rfl
@[m2_simp] theorem zz_pos (n : Int) : evalUnOp .pos (.zz n) = .ok (.zz n) := rfl

@[m2_simp] theorem qq_quot (p q : Rat) :
    evalBinOp .quot (.qq p) (.qq q) = .ok (.qq (if q = 0 then 0 else p / q)) := rfl
@[m2_simp] theorem qq_zz_quot (p : Rat) (n : Int) :
    evalBinOp .quot (.qq p) (.zz n) = .ok (.qq (if n = 0 then 0 else p / n)) := rfl
@[m2_simp] theorem qq_rem (p q : Rat) :
    evalBinOp .rem (.qq p) (.qq q) = .ok (.qq (if q = 0 then p else 0)) := rfl
@[m2_simp] theorem qq_zz_rem (p : Rat) (n : Int) :
    evalBinOp .rem (.qq p) (.zz n) = .ok (.qq (if n = 0 then p else 0)) := rfl

@[m2_simp] theorem qq_pow (p : Rat) (n : Int) :
    evalBinOp .pow (.qq p) (.zz n) =
      (if n < 0 ∧ p = 0 then .error .divByZero else .ok (.qq (p ^ n))) := rfl

end Macaulean.M2.Handles
