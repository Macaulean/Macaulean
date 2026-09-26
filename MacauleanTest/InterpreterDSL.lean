import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Run

/-!
# M2, without the quotation marks

Open this file in Lean. After `open M2`, the worksheet is ordinary M2 input.
The docstrings are executable output expectations, not hand-maintained screenshots.
No Macaulay2 executable, server, or network is needed for this file.

The last sections test the actual category/parser boundary, original source
positions, snapshots, error recovery, and coexistence with ordinary Lean.
-/

namespace M2WorksheetTest
open M2

-- A tiny notebook: variables survive from one Lean command to the next.
/-- info: o1 = 3 : ZZ -/
#guard_msgs in
x = 3

/-- info: o2 = 12 : ZZ -/
#guard_msgs in
y = x * 4

/-- info: o3 = 12 : ZZ -/
#guard_msgs in
y

-- Rebinding is M2 state, not a duplicate Lean declaration.
/-- info: o4 = 5 : ZZ -/
#guard_msgs in
x = x + 2

/-- info: o5 = 17 : ZZ -/
#guard_msgs in
x + y

-- M2 and Lean identifiers live in different environments.
def x : Nat := 100
example : x = 100 := rfl

/-- info: o6 = 5 : ZZ -/
#guard_msgs in
x

-- Semicolons really suppress output; every input still gets an input number.
#guard_msgs in
secret = 41;

/-- info: o8 = 42 : ZZ -/
#guard_msgs in
secret + 1

-- Two suppressed commands on the SAME source line.
a = 5; b = a^2;

/-- info: o11 = 25 : ZZ -/
#guard_msgs in
b

-- An assignment is an expression; assignments associate right.
/-- info: o12 = 9 : ZZ -/
#guard_msgs in
left = right = 9

/-- info: o13 = 18 : ZZ -/
#guard_msgs in
left + right

-- Parenthesized assignments, and left-to-right environment threading.
/-- info: o14 = 6 : ZZ -/
#guard_msgs in
(counter = 3) + counter

/-- info: o15 = 3 : ZZ -/
#guard_msgs in
counter

-- QQ remains distinct from ZZ, including integral-valued rationals.
/-- info: o16 = 1/2 : QQ -/
#guard_msgs in
half = 1/2

/-- info: o17 = 5/6 : QQ -/
#guard_msgs in
half + 1/3

/-- info: o18 = 1/1 : QQ -/
#guard_msgs in
7/7

/-- info: o19 = true : Boolean -/
#guard_msgs in
1 == 1/1

/-- info: o20 = 7/4 : QQ -/
#guard_msgs in
(7/2)//2

/-- info: o21 = 0/1 : QQ -/
#guard_msgs in
(7/2)%2

-- This is M2 precedence, not Lean's arithmetic syntax.
/-- info: o22 = 64 : ZZ -/
#guard_msgs in
2^3^2

/-- info: o23 = -4 : ZZ -/
#guard_msgs in
-2^2

/-- info: o24 = -2 : ZZ -/
#guard_msgs in
-7//3

/-- info: o25 = -3 : ZZ -/
#guard_msgs in
(-7)//3

/-- info: o26 = -7 : ZZ -/
#guard_msgs in
2 * -7 // 2

/-- info: o27 = -18 : ZZ -/
#guard_msgs in
2 * -3 ^ 2

/-- info: o28 = 1/16 : QQ -/
#guard_msgs in
2^-2^2

/-- info: o29 = -5 : ZZ -/
#guard_msgs in
2-3-4

/-- info: o30 = 1 : ZZ -/
#guard_msgs in
0^0

/-- info: o31 = 4/1 : QQ -/
#guard_msgs in
(1/2)^-2

-- Euclidean quotients and remainders, including negative divisors and zero.
/-- info: o32 = 2 : ZZ -/
#guard_msgs in
(-7)%3

/-- info: o33 = -2 : ZZ -/
#guard_msgs in
7//(-3)

/-- info: o34 = 1 : ZZ -/
#guard_msgs in
7%(-3)

/-- info: o35 = 3 : ZZ -/
#guard_msgs in
(-7)//(-3)

/-- info: o36 = 2 : ZZ -/
#guard_msgs in
(-7)%(-3)

/-- info: o37 = 0 : ZZ -/
#guard_msgs in
10//0

/-- info: o38 = -10 : ZZ -/
#guard_msgs in
(-10)%0

-- Newlines are part of the language, not just Lean layout.
/-- info: o39 = 3 : ZZ -/
#guard_msgs in
1 +
2

/-- info: o40 = 3 : ZZ -/
#guard_msgs in
(1
+2)

/-- info: o41 = 9 : ZZ -/
#guard_msgs in
(1 + -- a UTF-8 comment: λ, 中文
 2) * 3

-- Here the newline ENDS the first input, despite the following plus sign.
/-- info: o42 = 1 : ZZ -/
#guard_msgs in
1
/-- info: o43 = 2 : ZZ -/
#guard_msgs in
+2

-- The reader must not interpret `--` as two negations.
/-- info: o44 = 3 : ZZ -/
#guard_msgs in
3 -- - 1000000

-- Nondecimal literals and M2-style names.
/-- info: o45 = 51 : ZZ -/
#guard_msgs in
0x1F + 0b101 + 0o17

/-- info: o46 = 13 : ZZ -/
#guard_msgs in
value' = 13

/-- info: o47 = 14 : ZZ -/
#guard_msgs in
value$2 = value' + 1

/-- info: o48 = 14 : ZZ -/
#guard_msgs in
value$2

-- Comparisons and Boolean values.
/-- info: o49 = true : Boolean -/
#guard_msgs in
2 < 5/2

/-- info: o50 = false : Boolean -/
#guard_msgs in
3 >= 4

/-- info: o51 = true : Boolean -/
#guard_msgs in
true != false

-- Failure is visible, does not kill the worksheet, and is not a value.
/-- error: division by zero -/
#guard_msgs in
1/0

/-- info: o53 = 17 : ZZ -/
#guard_msgs in
x + y

/-- error: no method for operator // applied to objects of class ZZ, QQ -/
#guard_msgs in
3//(1/2)

/-- error: no method for operator == applied to objects of class ZZ, Boolean -/
#guard_msgs in
1 < 2 == true

/-- error: attempted to modify a protected symbol 'true' -/
#guard_msgs in
true = 3

/-- info: o57 = true : Boolean -/
#guard_msgs in
true

-- Failed assignments leave earlier bindings intact.
/-- error: division by zero -/
#guard_msgs in
x = 1/0

/-- info: o59 = 5 : ZZ -/
#guard_msgs in
x

-- Big integers do not overflow a machine word.
/-- info: o60 = 0 : ZZ -/
#guard_msgs in
3^2000 - 3^2000

-- Lean theorems remain ordinary Lean commands with ordinary Lean parsing.
example : Macaulean.M2.run "2^3^2" = .ok (.zz 64) := by decide +kernel
example : Macaulean.M2.run "2 * -7 // 2" = .ok (.zz (-7)) := by decide +kernel
example : Macaulean.M2.run "1/2 + 1/3" = .ok (.qq (mkRat 5 6)) := by decide +kernel

end M2WorksheetTest

namespace M2ReaderTest
open Lean Elab Command

-- The actual syntax category lowers to the same AST as the old string API.
run_cmd do
  let sources := #[
    "0", "0x1F", "0b101", "0o17", "value'", "value$2",
    "(-7)//3", "-7//3", "2 * -7 // 2", "2^-2^2", "2^3^2",
    "2 * -3 ^ 2", "-2+3", "2-3-4", "x = y = 3", "(x) = 3",
    "1/2 + 1/3", "1 < 2 == true", "(1\n+2)", "1 +\n2",
    "(1 + -- λ\n 2) * 3", "x = 3;"
  ]
  for source in sources do
    let stx ← match Parser.runParserCategory (← getEnv) `m2 source with
      | .ok stx => pure stx
      | .error error => throwError "M2 category rejected {repr source}: {error}"
    let (term, silent) ← match Macaulean.M2.DSL.lowerInput ⟨stx⟩ with
      | .ok result => pure result
      | .error error => throwError "M2 lowering failed: {error}"
    let expected ← match Macaulean.M2.parse source with
      | .ok term => pure term
      | .error error => throwError "string parser failed: {error}"
    unless term == expected do
      throwError "different ASTs for {repr source}: {repr term} versus {repr expected}"
    unless silent == source.endsWith ";" do
      throwError "wrong terminator for {repr source}"

-- Rejected inputs are tested through the same pure reader, without requiring a
-- deliberately malformed Lean file or depending on Lean parser-recovery wording.
run_cmd do
  for source in #["", "1;;", "(1 + 2", "1.5", "1 2", "2 = 3", "1 +", ";", "1 $ 2"] do
    -- `1;;` consists of one valid input followed by an invalid second input.
    if source == "1;;" then
      let .ok first := Macaulean.M2.Input.parse source | throwError "first input should parse"
      let tail := String.Pos.Raw.extract source ⟨first.tokens.stop⟩ source.rawEndPos
      if (Macaulean.M2.Input.parse tail).isOk then throwError "accepted empty second input"
    else if (Macaulean.M2.Input.parse source).isOk then
      throwError "reader accepted invalid input {repr source}"

-- CRLF, operator continuation, and first-input boundaries.
run_cmd do
  for (source, expected) in #[
    ("1\r\n+2", Macaulean.M2.Term.int 1),
    ("1 +\r\n2", Macaulean.M2.Term.binop .add (.int 1) (.int 2)),
    ("1;2", Macaulean.M2.Term.int 1)
  ] do
    let .ok parsed := Macaulean.M2.Input.parse source | throwError "input reader failed"
    unless parsed.tree.toTerm == expected do throwError "wrong boundary for {repr source}"

-- Original UTF-8 byte ranges survive a non-ASCII comment. The second number is
-- token 4: (, 1, +, newline, 2, ... . Counting characters instead of bytes fails.
run_cmd do
  let source := "(1 + -- λ, 中文\n 2) * 3"
  let .ok parsed := Macaulean.M2.Input.parse source | throwError "input reader failed"
  let span := parsed.tokens.located[4]!.span
  let original := String.Pos.Raw.extract source ⟨span.start⟩ ⟨span.stop⟩
  unless original == "2" do throwError "corrupt source range: {repr original}"
  let .ok stx := Parser.runParserCategory (← getEnv) `m2 source
    | throwError "category parser failed"
  let body := stx[0][0]
  unless body.getKind == `Macaulean.M2.DSL.binop do throwError "opaque/nonstructured syntax"
  let rhs := body[2][0][0]
  let some start := rhs.getPos? | throwError "missing number source position"
  let some stop := rhs.getTailPos? | throwError "missing number end position"
  unless String.Pos.Raw.extract source start stop == "3" do
    throwError "native syntax node does not point into the original source"

-- Retaining an old environment is enough to branch/replay a worksheet. These
-- assertions check value semantics of snapshots, not merely a mutable counter.
run_cmd do
  let original ← getEnv
  let s0 := Macaulean.M2.DSL.sessionExt.getState original
  let a := s0.step (.assign "snapshotVariable" (.int 7))
  let afterA := Macaulean.M2.DSL.sessionExt.setState original a.session
  let b := s0.step (.assign "snapshotVariable" (.int 19))
  let afterEdit := Macaulean.M2.DSL.sessionExt.setState original b.session
  let readA := (Macaulean.M2.DSL.sessionExt.getState afterA).step (.var "snapshotVariable")
  let readEdit := (Macaulean.M2.DSL.sessionExt.getState afterEdit).step (.var "snapshotVariable")
  unless readA.outcome == .ok (.zz 7) do throwError "old snapshot changed"
  unless readEdit.outcome == .ok (.zz 19) do throwError "edited snapshot not recomputed"
  unless (Macaulean.M2.DSL.sessionExt.getState original).env == s0.env do
    throwError "snapshot mutation leaked into the saved environment"

-- Closing the namespace disabled the scoped command bridge.
run_cmd do
  if (Parser.runParserCategory (← getEnv) `command "2 + 3").isOk then
    throwError "M2 top-level syntax leaked out of its scope"

end M2ReaderTest
