import Macaulean.Interpreter

/-!
Tests of the Macaulay2 interpreter that do not need Macaulay2.  The expected
values were obtained from Macaulay2 1.26.06.  Each is proved by kernel
evaluation of the lexer, parser and evaluator on the source string.
-/

open Macaulean.M2

-- `//` and `%` are Euclidean division
example : run "(-7)//3" = .ok (.zz (-3)) := by decide +kernel
example : run "(-7)%3" = .ok (.zz 2) := by decide +kernel
example : run "7//(-3)" = .ok (.zz (-2)) := by decide +kernel
example : run "7%(-3)" = .ok (.zz 1) := by decide +kernel
example : run "(-7)//(-3)" = .ok (.zz 3) := by decide +kernel
example : run "(-7)%(-3)" = .ok (.zz 2) := by decide +kernel
example : run "10//0" = .ok (.zz 0) := by decide +kernel
example : run "(-10)%0" = .ok (.zz (-10)) := by decide +kernel

-- `/` lands in QQ, even when the quotient is an integer
example : run "7/2" = .ok (.qq (mkRat 7 2)) := by decide +kernel
example : run "7/7" = .ok (.qq 1) := by decide +kernel
example : run "1/2 + 1/3" = .ok (.qq (mkRat 5 6)) := by decide +kernel
example : run "7/0" = .error .divByZero := by decide +kernel
example : run "(7/2)//2" = .ok (.qq (mkRat 7 4)) := by decide +kernel
example : run "(7/2)%0" = .ok (.qq (mkRat 7 2)) := by decide +kernel
example : run "3//(1/2)" = .error (.noMethod "//" ["ZZ", "QQ"]) := by decide +kernel

-- powers
example : run "2^-2" = .ok (.qq (mkRat 1 4)) := by decide +kernel
example : run "0^0" = .ok (.zz 1) := by decide +kernel
example : run "0^-1" = .error .divByZero := by decide +kernel
example : run "(1/2)^-2" = .ok (.qq 4) := by decide +kernel
example : run "3^2000 - 3^2000" = .ok (.zz 0) := by decide +kernel

-- precedence and associativity
example : run "2^3^2" = .ok (.zz 64) := by decide +kernel
example : run "-2^2" = .ok (.zz (-4)) := by decide +kernel
example : run "-7//3" = .ok (.zz (-2)) := by decide +kernel
example : run "-7%3" = .ok (.zz (-1)) := by decide +kernel
example : run "2 * -7 // 2" = .ok (.zz (-7)) := by decide +kernel
example : run "2 * - 3 ^ 2" = .ok (.zz (-18)) := by decide +kernel
example : run "2^-2^2" = .ok (.qq (mkRat 1 16)) := by decide +kernel
example : run "-2+3" = .ok (.zz 1) := by decide +kernel
example : run "2-3-4" = .ok (.zz (-5)) := by decide +kernel
example : run "1 < 2 == true" = .error (.noMethod "==" ["ZZ", "Boolean"]) := by decide +kernel

-- comparisons
example : run "1 == 1/1" = .ok (.bool true) := by decide +kernel
example : run "2 < 5/2" = .ok (.bool true) := by decide +kernel
example : run "3 >= 4" = .ok (.bool false) := by decide +kernel

-- literals, comments
example : run "0x1F + 0b101 + 0o17" = .ok (.zz 51) := by decide +kernel
example : run "-- c\n2 -- d" = .ok (.zz 2) := by decide +kernel

-- statements, variables and newlines
example : run "x = 3; y = x * 4; y" = .ok (.zz 12) := by decide +kernel
example : run "x = y = 3; x+y" = .ok (.zz 6) := by decide +kernel
example : run "x = 3;" = .ok (.zz 3) := by decide +kernel
example : run "" = .ok .null := by decide +kernel
example : run "1\n+2" = .ok (.zz 2) := by decide +kernel
example : run "1 +\n2" = .ok (.zz 3) := by decide +kernel
example : run "(1\n+2)" = .ok (.zz 3) := by decide +kernel
example : run "1;\n2" = .ok (.zz 2) := by decide +kernel
example : run "y" = .error (.unboundVar "y") := by decide +kernel
example : run "true = 3" = .error (.protectedSymbol "true") := by decide +kernel

-- parse errors
example : ∃ msg, run "1;;" = .parseError msg := ⟨_, rfl⟩
example : ∃ msg, run "(1 + 2" = .parseError msg := ⟨_, rfl⟩
example : ∃ msg, run "1.5" = .parseError msg := ⟨_, rfl⟩

/-- info: -11/4 -/
#guard_msgs in
#m2_eval "(-7)//3 + 2^-2"

/-- info: error: division by zero -/
#guard_msgs in
#m2_eval "1/0"

-- printing a term and parsing it back gives the same term
def roundTrips (s : String) : Bool :=
  match parse s with
  | .ok t => parse t.toM2String == .ok t
  | .error _ => false

#guard roundTrips "-7//3 + 2 * -7 // 2 - 2^-2^2"
#guard roundTrips "x = y = 3; x + y < 7 == true"
#guard roundTrips "(1 +\n 2) * -(3 - 4)"
