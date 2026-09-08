/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.PolyDef

/-!
# Tests for `poly_def`

`poly_def` is type- and variable-agnostic: here the ambient type is `Int` and
the "variables" are `Int` terms, so every definition evaluates to a numeral
and can be checked by `decide`/`rfl`.  Mathlib-free.
-/

namespace MacauleanTest.PolyDef

/-- 3 variables: `2 + 3 + 5`. -/
poly_def sum3 : Int in [2, 3, 5] := "1.0.0.1 0.1.0.1 0.0.1.1"

example : sum3 = 10 := by decide

/-- 3 variables with a negative coefficient: `3 * 2^2 - 4 * 3 * 5`. -/
poly_def negCoeff : Int in [2, 3, 5] := "2.0.0.3 0.1.1.-4"

example : negCoeff = -48 := rfl

/-- A leading negative coefficient and a constant term: `-2 * 2^3 + 5`. -/
poly_def negLead : Int in [2] := "3.-2 0.5"

example : negLead = -11 := rfl

/-- One variable, several powers: `2^4 + 7 * 2^2 - 2`. -/
poly_def onevar : Int in [2] := "4.1 2.7 1.-1"

example : onevar = 42 := by decide

/-- The variable terms are arbitrary terms of the ascribed type. -/
poly_def compound : Int in [1 + 1, 10 - 4] := "1.1.1 0.0.-5"

example : compound = 7 := rfl

/-- The generated body is the same term source syntax would produce. -/
theorem shape : negCoeff = 3 * (2 : Int) ^ 2 - 4 * 3 * 5 := rfl

/-- info: def MacauleanTest.PolyDef.negCoeff : Int :=
3 * 2 ^ 2 - 4 * 3 * 5 -/
#guard_msgs in
#print negCoeff

/-- The doc string of this definition survives. -/
poly_def documented : Int in [2, 3] := "1.1.6"

example : documented = 36 := by decide

end MacauleanTest.PolyDef
