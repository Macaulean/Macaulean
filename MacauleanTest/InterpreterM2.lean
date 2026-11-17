import Macaulean.Interpreter

/-!
Differential tests: each `#m2_check` evaluates the source with both the Lean
interpreter and a live Macaulay2, fails if they disagree, and otherwise adds a
kernel-checked theorem `run src = outcome`.
-/

namespace Macaulean.M2.Test

/-- info: euclid : run "(-7)//3 + (-7)%3" = -1 -/
#guard_msgs in
#m2_check euclid : "(-7)//3 + (-7)%3"

/-- info: rational : run "(-7)//3 + 2^-2" = -11/4 -/
#guard_msgs in
#m2_check rational : "(-7)//3 + 2^-2"

/-- info: qq_one : run "7/7" = 1/1 -/
#guard_msgs in
#m2_check qq_one : "7/7"

/-- info: div_zero : run "7/0" = error: division by zero -/
#guard_msgs in
#m2_check div_zero : "7/0"

/-- info: big : run "2^200 // 3^50" = 2238393297946874000179418290327143433 -/
#guard_msgs in
#m2_check big : "2^200 // 3^50"

/-- info: unary_minus : run "2 * -7 // 2 - -7//3" = -5 -/
#guard_msgs in
#m2_check unary_minus : "2 * -7 // 2 - -7//3"

/-- info: statements : run "a = 5; b = a^2\nb == 25" = true -/
#guard_msgs in
#m2_check statements : "a = 5; b = a^2\nb == 25"

/-- info: literals : run "0x1F + 0b101 + 0o17 - 0" = 51 -/
#guard_msgs in
#m2_check literals : "0x1F + 0b101 + 0o17 - 0"

/-- info: m2_check_1 : run "(1/2)^-3 * 5 % 2" = 0/1 -/
#guard_msgs in
#m2_check "(1/2)^-3 * 5 % 2"

example : run "(-7)//3 + 2^-2" = .ok (.qq (mkRat (-11) 4)) := rational


-- Check the same regression cases against live M2, including result classes.
/-- info: semantics_regression_1 : run "1^-1" = 1 -/
#guard_msgs in
#m2_check semantics_regression_1 : "1^-1"

/-- info: semantics_regression_2 : run "(-1)^-1" = -1 -/
#guard_msgs in
#m2_check semantics_regression_2 : "(-1)^-1"

/-- info: semantics_regression_3 : run "(-1)^-2" = 1 -/
#guard_msgs in
#m2_check semantics_regression_3 : "(-1)^-2"

/-- info: semantics_regression_4 : run "3 // (1^-1)" = 3 -/
#guard_msgs in
#m2_check semantics_regression_4 : "3 // (1^-1)"

/-- info: semantics_regression_5 : run "2^(2/1)" = 4 -/
#guard_msgs in
#m2_check semantics_regression_5 : "2^(2/1)"

/-- info: semantics_regression_6 : run "2^(-1/1)" = 1/2 -/
#guard_msgs in
#m2_check semantics_regression_6 : "2^(-1/1)"

/-- info: semantics_regression_7 : run "(1/2)^(2/1)" = 1/4 -/
#guard_msgs in
#m2_check semantics_regression_7 : "(1/2)^(2/1)"

/-- info: semantics_regression_8 : run "(2/1)^(2/1)" = 4/1 -/
#guard_msgs in
#m2_check semantics_regression_8 : "(2/1)^(2/1)"

/-- info: semantics_regression_9 : run "(-1)^(-3/1)" = -1/1 -/
#guard_msgs in
#m2_check semantics_regression_9 : "(-1)^(-3/1)"

/-- info: semantics_regression_10 : run "1^(0/1)" = 1 -/
#guard_msgs in
#m2_check semantics_regression_10 : "1^(0/1)"

/-- info: semantics_regression_11 : run "(1/1)^(-1/1)" = 1/1 -/
#guard_msgs in
#m2_check semantics_regression_11 : "(1/1)^(-1/1)"

/-- info: semantics_regression_12 : run "0^(-1/1)" = error: division by zero -/
#guard_msgs in
#m2_check semantics_regression_12 : "0^(-1/1)"

/-- info: semantics_regression_13 : run "true < true" = false -/
#guard_msgs in
#m2_check semantics_regression_13 : "true < true"

/-- info: semantics_regression_14 : run "true <= true" = true -/
#guard_msgs in
#m2_check semantics_regression_14 : "true <= true"

/-- info: semantics_regression_15 : run "true > true" = false -/
#guard_msgs in
#m2_check semantics_regression_15 : "true > true"

/-- info: semantics_regression_16 : run "true >= true" = true -/
#guard_msgs in
#m2_check semantics_regression_16 : "true >= true"

/-- info: semantics_regression_17 : run "true < false" = error: no method for operator < applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_17 : "true < false"

/-- info: semantics_regression_18 : run "true <= false" = error: no method for operator <= applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_18 : "true <= false"

/-- info: semantics_regression_19 : run "true > false" = error: no method for operator > applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_19 : "true > false"

/-- info: semantics_regression_20 : run "true >= false" = error: no method for operator >= applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_20 : "true >= false"

/-- info: semantics_regression_21 : run "false < true" = error: no method for operator < applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_21 : "false < true"

/-- info: semantics_regression_22 : run "false <= true" = error: no method for operator <= applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_22 : "false <= true"

/-- info: semantics_regression_23 : run "false > true" = error: no method for operator > applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_23 : "false > true"

/-- info: semantics_regression_24 : run "false >= true" = error: no method for operator >= applied to objects of class Boolean, Boolean -/
#guard_msgs in
#m2_check semantics_regression_24 : "false >= true"

/-- info: semantics_regression_25 : run "false < false" = false -/
#guard_msgs in
#m2_check semantics_regression_25 : "false < false"

/-- info: semantics_regression_26 : run "false <= false" = true -/
#guard_msgs in
#m2_check semantics_regression_26 : "false <= false"

/-- info: semantics_regression_27 : run "false > false" = false -/
#guard_msgs in
#m2_check semantics_regression_27 : "false > false"

/-- info: semantics_regression_28 : run "false >= false" = true -/
#guard_msgs in
#m2_check semantics_regression_28 : "false >= false"

/-- info: semantics_regression_29 : run "1^(-1/1)" = 1/1 -/
#guard_msgs in
#m2_check semantics_regression_29 : "1^(-1/1)"

/-- info: semantics_regression_30 : run "(-1)^(-2/1)" = 1/1 -/
#guard_msgs in
#m2_check semantics_regression_30 : "(-1)^(-2/1)"

end Macaulean.M2.Test
