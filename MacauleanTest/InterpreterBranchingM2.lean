import Macaulean.Interpreter.Check

/-!
# Independent native-M2 comparisons

All value probes below must SUCCEED on both interpreters with identical values
and classes. Two unrelated errors cannot make these tests pass. Each stateful
probe initializes all its variables so M2's persistent test server cannot leak
state into the comparison with the fresh Lean `run` environment.

The final probes inspect native `parse` trees, independently of computed values:
Boolean truth tables alone cannot distinguish left and right association.
External M2 is confined to tests, never the DSL implementation.
-/

namespace Macaulean.M2.BranchingM2Test
open Lean Elab Command

run_cmd do
  for source in #[
    "if true then 7 else 1/0",
    "if false then 1/0 else 7",
    "if false then 1/0",
    "if true then 7",
    "if true then 1/2 else 1/0",
    "if true then if false then 1 else 2",
    "if false then if true then 1 else 2",
    "if false then if true then 1 else 2 else 3",
    "x = if false then 1 else 2; x",
    "if true then x = 7 else x = 99; x",
    "1 + if true then 2 else 3 + 4",
    "if false then 1 else 2 + 3 * 4",
    "false and 1/0", "true or 1/0", "false and 99", "true or 99",
    "true and false", "false or true", "true and true", "false or false",
    "not true", "not not true", "not 1 == 1",
    "false and true or true", "true or false and 1/0", "not false and true",
    "x = 0; if false then (x = 99); x",
    "x = 0; if true then (x = 3; x + 4) else (x = 99); x",
    "if (x = 3; x > 0) then x + 4 else 1/0",
    "x = 0; false and (x = 99; true); x",
    "x = 0; true or (x = 99; false); x",
    "x = 0; true and (x = 3; true); x",
    "x = 0; false or (x = 4; false); x",
    "(x = 2; false) and (x = 99; true); x",
    "(x = 2; true) or (x = 99; false); x",
    "(x = 3; y = x + 4; y)", "(x = 3; (x = x + 1; x * 2))",
    "(1;)", "(1; 2;)", "(x = 3;); x", "1 + (x = 3; x)", "7;",
    "null", "null == null", "null != null", "if false then null = 3",
    "if\n1 <\n2\nthen\n7", "(if true then 1\nelse 2)",
    "if true then 1\n+2", "true and\nfalse", "not\nfalse", "(x = 1;\nx + 2)",
    "ifx = 3; then$1 = ifx; not' = then$1; not'"
  ] do
    let .ok expected := run source
      | throwError "positive Lean probe failed: {repr source}: {repr (run source)}"
    match ← queryM2 source with
    | .ok (.ok actual) =>
      unless actual == expected do
        throwError "M2 value/class mismatch on {repr source}: Lean {repr expected}, M2 {repr actual}"
    | .ok .error => throwError "native M2 rejected positive probe {repr source}"
    | .error message => throwError "native M2 query failed: {message}"

-- Native error controls. These are separate from the positive comparisons and
-- supplement, rather than replace, the precise kernel-checked Lean error tests.
run_cmd do
  for source in #["if 1 then 2 else 3", "if null then 2", "true and 7", "false or null",
    "not 7", "null = 3", "true and 1/0", "false or 1/0", "if true then 1/0 else 7"] do
    let .error _ := run source | throwError "Lean did not raise a runtime error for {repr source}"
    match ← queryM2 source with
    | .ok .error => pure ()
    | .ok (.ok value) => throwError "native M2 unexpectedly returned {repr value} for {repr source}"
    | .error message => throwError "native M2 query failed: {message}"

-- Check native concrete syntax, including dangling else and Boolean association.
-- t is the first statement of M2's documented list-valued `parse` result.
run_cmd do
  for (source, predicate) in #[
    ("if a then if b then 1 else 2",
      "toString(t#0) == \"IfThen\" and toString(t#2#0) == \"IfThenElse\""),
    ("if a then if b then 1 else 2 else 3",
      "toString(t#0) == \"IfThenElse\" and toString(t#2#0) == \"IfThenElse\""),
    ("a and b and c",
      "toString(t#0) == \"Binary\" and toString(t#3#0) == \"Binary\" and toString(t#2#1) == \"and\""),
    ("a or b or c",
      "toString(t#0) == \"Binary\" and toString(t#3#0) == \"Binary\" and toString(t#2#1) == \"or\""),
    ("not a == b",
      "toString(t#0) == \"Unary\" and toString(t#2#0) == \"Binary\" and toString(t#1#1) == \"not\""),
    ("a or b and c",
      "toString(t#2#1) == \"or\" and toString(t#3#2#1) == \"and\"")
  ] do
    let quoted := (Json.str source).compress
    let probe := s!"(t := (parse {quoted})#0; {predicate})"
    match ← queryM2 probe with
    | .ok (.ok (.bool true)) => pure ()
    | .ok reply => throwError "native parser shape disagrees for {repr source}: {reply.toM2String}"
    | .error message => throwError "native parse query failed: {message}"

end Macaulean.M2.BranchingM2Test
