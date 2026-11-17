import Macaulean.Verification.Handles

/-! Rational handle proofs exercise symbolic arguments, mixed runtime numeric
classes, branch-local division safety, and calls across worksheet states. -/
open M2 Macaulean.M2

#guard_msgs in
averageQ = (x,y) -> (x + y) / 2;

theorem averageQ_spec (x y : Rat) : averageQ (x, y) ⇓ (x + y) / 2 := by
  m2_unfold

#guard_msgs in
mixedQ = (x,n) -> (n + x) * (x - n);

example (x : Rat) (n : Int) : mixedQ (x, n) ⇓ ((n : Rat) + x) * (x - n) := by
  m2_unfold

#guard_msgs in
quotientQ = (x,y) -> x / y;

theorem quotientQ_spec (x y : Rat) (hy : y ≠ 0) : quotientQ (x, y) ⇓ x / y := by
  m2_unfold

-- Missing bounds must remain a proof obligation, never silently disappear.
example (x y : Rat) (h : y ≠ 0) : quotientQ (x, y) ⇓ x / y := by
  revert h
  intro hy
  fail_if_success solve | (clear hy; m2_unfold)
  m2_unfold

#guard_msgs in
safeQuotientQ = (x,y) -> if y == 0 then x else x / y;

example (x y : Rat) : safeQuotientQ (x, y) ⇓ (if y = 0 then x else x / y) := by
  m2_unfold
  split <;> simp_all

#guard_msgs in
averageTwiceQ = (x,y) -> averageQ(x,y) + averageQ(y,x);

example (x y : Rat) : averageTwiceQ (x, y) ⇓ x + y := by
  m2_unfold
  m2_use averageQ_spec x y
  m2_use averageQ_spec y x
  grind

#guard_msgs in
lessQ = (x,y) -> x < y;
#guard_msgs in
compareMixedQ = (x,n) -> x >= n and n <= x;
#guard_msgs in
negateQ = x -> -x;
#guard_msgs in
positiveQ = x -> +x;

example (x y : Rat) : lessQ (x, y) ⇓ decide (x < y) := by m2_unfold
example (x : Rat) (n : Int) : compareMixedQ (x, n) ⇓ decide ((n : Rat) ≤ x) := by
  m2_unfold
example (x : Rat) : negateQ x ⇓ -x := by m2_unfold
example (x : Rat) : positiveQ x ⇓ x := by m2_unfold

#guard_msgs in
quotQ = (x,y) -> x // y;
#guard_msgs in
remQ = (x,y) -> x % y;
#guard_msgs in
powerQ = (x,n) -> x^n;

example (x y : Rat) : quotQ (x, y) ⇓ (if y = 0 then 0 else x / y) := by m2_unfold
example (x y : Rat) : remQ (x, y) ⇓ (if y = 0 then x else 0) := by m2_unfold
example (x : Rat) (n : Int) (h : x ≠ 0) : powerQ (x, n) ⇓ x ^ n := by
  m2_unfold
  simp_all
example : averageQ ((1 : Rat), (2 : Rat)) ⇓ (3 / 2 : Rat) := by m2_eval

-- Errors are checked against the actual operator, including unsupported dispatch.
example (x : Rat) : evalBinOp .div (.qq x) (.qq 0) = .error .divByZero := by
  simp [Handles.qq_div]
example (x : Rat) : evalBinOp .quot (.qq x) (.qq 0) = .ok (.qq 0) := rfl
example (x : Rat) : evalBinOp .rem (.qq x) (.qq 0) = .ok (.qq x) := rfl
example : evalBinOp .pow (.qq 0) (.zz (-1)) = .error .divByZero := by decide
example : evalBinOp .quot (.zz 1) (.qq 2) = .error (.noMethod "//" ["ZZ", "QQ"]) := by decide

/-- info: 'averageQ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms averageQ_spec
