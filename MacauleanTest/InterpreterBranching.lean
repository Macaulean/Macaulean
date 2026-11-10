import Macaulean.Interpreter.Run
import Macaulean.Interpreter.ControlFlow

/-!
Kernel checks for the branching fragment. Bad syntax is tested by its error
constructor, so no proof relies on reducing Lean's opaque `Repr` formatter.
-/

namespace Macaulean.M2.BranchingTest

-- Only the selected branch runs.
example : run "if true then 7 else 1/0" = .ok (.zz 7) := by decide +kernel
example : run "if false then 1/0 else 7" = .ok (.zz 7) := by decide +kernel
example : run "if false then 1/0" = .ok .null := by decide +kernel
example : run "if true then 7" = .ok (.zz 7) := by decide +kernel
example : run "if true then 1/2 else 1/0" = .ok (.qq (mkRat 1 2)) := by decide +kernel
example : run "if 1 then 2 else 3" = .error (.conditionNotBoolean "ZZ") := by decide +kernel
example : run "if 0/1 then 2" = .error (.conditionNotBoolean "QQ") := by decide +kernel
example : run "if null then 2" = .error (.conditionNotBoolean "Nothing") := by decide +kernel
example : run "if 1/0 then 2 else 3" = .error .divByZero := by decide +kernel
example : run "if true then 1/0 else 3" = .error .divByZero := by decide +kernel

-- Dangling else, branch assignment and wide branch precedence.
example : run "if true then if false then 1 else 2" = .ok (.zz 2) := by decide +kernel
example : run "if false then if true then 1 else 2" = .ok .null := by decide +kernel
example : run "if false then if true then 1 else 2 else 3" = .ok (.zz 3) := by decide +kernel
example : run "x = if false then 1 else 2; x" = .ok (.zz 2) := by decide +kernel
example : run "if true then x = 7 else x = 99; x" = .ok (.zz 7) := by decide +kernel
example : run "1 + if true then 2 else 3 + 4" = .ok (.zz 3) := by decide +kernel
example : run "if false then 1 else 2 + 3 * 4" = .ok (.zz 14) := by decide +kernel

-- Strict Boolean methods and genuinely lazy right operands.
example : run "false and 1/0" = .ok (.bool false) := by decide +kernel
example : run "true or 1/0" = .ok (.bool true) := by decide +kernel
example : run "false and 99" = .ok (.bool false) := by decide +kernel
example : run "true or 99" = .ok (.bool true) := by decide +kernel
example : run "true and false" = .ok (.bool false) := by decide +kernel
example : run "false or true" = .ok (.bool true) := by decide +kernel
example : run "true and 1/0" = .error .divByZero := by decide +kernel
example : run "false or 1/0" = .error .divByZero := by decide +kernel
example : run "true and 7" = .error (.noMethod "and" ["Boolean", "ZZ"]) := by decide +kernel
example : run "false or null" = .error (.noMethod "or" ["Boolean", "Nothing"]) := by decide +kernel
example : run "not 7" = .error (.noMethod "not" ["ZZ"]) := by decide +kernel
example : run "not true" = .ok (.bool false) := by decide +kernel
example : run "not not true" = .ok (.bool true) := by decide +kernel
example : run "not 1 == 1" = .ok (.bool false) := by decide +kernel
example : run "false and true or true" = .ok (.bool true) := by decide +kernel
example : run "true or false and 1/0" = .ok (.bool true) := by decide +kernel
example : run "not false and true" = .ok (.bool true) := by decide +kernel

-- Blocks do not introduce scope. Conditions and operands can change bindings.
example : run "x = 0; if false then (x = 99); x" = .ok (.zz 0) := by decide +kernel
example : run "x = 0; if true then (x = 3; x + 4) else (x = 99); x" = .ok (.zz 3) := by decide +kernel
example : run "if (x = 3; x > 0) then x + 4 else 1/0" = .ok (.zz 7) := by decide +kernel
example : run "x = 0; false and (x = 99; true); x" = .ok (.zz 0) := by decide +kernel
example : run "x = 0; true or (x = 99; false); x" = .ok (.zz 0) := by decide +kernel
example : run "x = 0; true and (x = 3; true); x" = .ok (.zz 3) := by decide +kernel
example : run "x = 0; false or (x = 4; false); x" = .ok (.zz 4) := by decide +kernel
example : run "(x = 2; false) and (x = 99; true); x" = .ok (.zz 2) := by decide +kernel
example : run "(x = 2; true) or (x = 99; false); x" = .ok (.zz 2) := by decide +kernel
example : run "(x = 3; y = x + 4; y)" = .ok (.zz 7) := by decide +kernel
example : run "(x = 3; (x = x + 1; x * 2))" = .ok (.zz 8) := by decide +kernel
example : run "(1;)" = .ok .null := by decide +kernel
example : run "(1; 2;)" = .ok .null := by decide +kernel
example : run "(x = 3;); x" = .ok (.zz 3) := by decide +kernel
example : run "1 + (x = 3; x)" = .ok (.zz 4) := by decide +kernel
example : run "(1/0; 7)" = .error .divByZero := by decide +kernel
-- Keep the parent API's top-level `value` convention.
example : run "7;" = .ok (.zz 7) := by decide +kernel

-- Null is a protected value; no-else does not fabricate a variable lookup.
example : run "null" = .ok .null := by decide +kernel
example : run "null == null" = .ok (.bool true) := by decide +kernel
example : run "null != null" = .ok (.bool false) := by decide +kernel
example : run "null = 3" = .error (.protectedSymbol "null") := by decide +kernel
example : run "if false then null = 3" = .ok .null := by decide +kernel

-- Newline continuation is M2's, not Lean's if-expression layout.
example : run "if\n1 <\n2\nthen\n7" = .ok (.zz 7) := by decide +kernel
example : run "(if true then 1\nelse 2)" = .ok (.zz 1) := by decide +kernel
example : run "if true then 1\n+2" = .ok (.zz 2) := by decide +kernel
example : run "true and\nfalse" = .ok (.bool false) := by decide +kernel
example : run "not\nfalse" = .ok (.bool true) := by decide +kernel
example : run "(x = 1;\nx + 2)" = .ok (.zz 3) := by decide +kernel
example : run "ifx = 3; then$1 = ifx; not' = then$1; not'" = .ok (.zz 3) := by decide +kernel

private def hasParseError (source : String) : Bool :=
  match run source with
  | .parseError _ => true
  | _ => false

example : hasParseError "if true" = true := by decide +kernel
example : hasParseError "if true then" = true := by decide +kernel
example : hasParseError "if true then 1 else" = true := by decide +kernel
example : hasParseError "if true then 1\nelse 2" = true := by decide +kernel
example : hasParseError "if true then 1 else (1 +)" = true := by decide +kernel
example : hasParseError "if true then 1 else (2 = 3)" = true := by decide +kernel
example : hasParseError "if = 3" = true := by decide +kernel
example : hasParseError "then = 3" = true := by decide +kernel
example : hasParseError "else = 3" = true := by decide +kernel
example : hasParseError "and = 3" = true := by decide +kernel
example : hasParseError "not = 3" = true := by decide +kernel
example : hasParseError "(x = 1\nx + 2)" = true := by decide +kernel
example : hasParseError "(1;;)" = true := by decide +kernel
example : hasParseError "(;1)" = true := by decide +kernel
-- Empty parentheses are a Sequence, outside this scalar fragment, not null.
example : hasParseError "()" = true := by decide +kernel

-- Structural parser checks, not just truth tables (which conceal association).
example : parse "true and false and true" = .ok
    (.logic .andOp (.var "true") (.logic .andOp (.var "false") (.var "true"))) := by
  decide +kernel
example : parse "false or true or false" = .ok
    (.logic .orOp (.var "false") (.logic .orOp (.var "true") (.var "false"))) := by
  decide +kernel
example : parse "if true then if false then 1 else 2" = .ok
    (.ifThen (.var "true") (.ifElse (.var "false") (.int 1) (.int 2))) := by
  decide +kernel
example : parse "(1; 2;)" = .ok (.seq (.int 1) (.seq (.int 2) .empty)) := by
  decide +kernel

end Macaulean.M2.BranchingTest
