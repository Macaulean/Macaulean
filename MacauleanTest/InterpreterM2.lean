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

end Macaulean.M2.Test
