import Macaulean.Interpreter.DSL
import Macaulean.Interpreter.Run

/-!
# A branching M2 notebook

This file is an executable worksheet. Move the cursor through the bare M2
inputs to see their outputs in InfoView. Every displayed result, and every
intentional absence of output, is checked by `#guard_msgs`.
-/

namespace BranchingWorksheet
open M2

#guard_msgs in
x = -7;

/-- info: o2 = 7 : ZZ -/
#guard_msgs in
magnitude = if x < 0 then -x else x

/-- info: o3 = true : Boolean -/
#guard_msgs in
magnitude == 7

#guard_msgs in
denominator = 0;

/-- info: o5 = false : Boolean -/
#guard_msgs in
safe = denominator != 0 and 1/denominator > 0

/-- info: o6 = 7 : ZZ -/
#guard_msgs in
if true then (x = 3; x + 4) else 1/0

/-- info: o7 = 3 : ZZ -/
#guard_msgs in
x

-- A skipped assignment has no effect; missing else returns silent null.
#guard_msgs in
if false then (x = 99)

/-- info: o9 = 3 : ZZ -/
#guard_msgs in
x

/-- info: o10 = 5/6 : QQ -/
#guard_msgs in
if false then 1/0 else (half = 1/2; half + 1/3)

/-- info: o11 = 1/2 : QQ -/
#guard_msgs in
half

/-- info: o12 = false : Boolean -/
#guard_msgs in
false and (x = 99; true)

/-- info: o13 = true : Boolean -/
#guard_msgs in
true or (x = 99; false)

/-- info: o14 = 3 : ZZ -/
#guard_msgs in
x

-- Effects of the evaluated LEFT operand must survive short-circuiting.
/-- info: o15 = false : Boolean -/
#guard_msgs in
(x = 4; false) and (x = 99; true)

/-- info: o16 = 4 : ZZ -/
#guard_msgs in
x

/-- info: o17 = true : Boolean -/
#guard_msgs in
(x = 5; true) or (x = 99; false)

/-- info: o18 = 5 : ZZ -/
#guard_msgs in
x

/-- info: o19 = true : Boolean -/
#guard_msgs in
true and (x = 6; true)

/-- info: o20 = false : Boolean -/
#guard_msgs in
false or (x = 7; false)

/-- info: o21 = 7 : ZZ -/
#guard_msgs in
x

-- M2 precedence and nearest-if attachment.
/-- info: o22 = false : Boolean -/
#guard_msgs in
not 1 == 1

/-- info: o23 = true : Boolean -/
#guard_msgs in
false and true or true

/-- info: o24 = true : Boolean -/
#guard_msgs in
true or false and 1/0

/-- info: o25 = true : Boolean -/
#guard_msgs in
not not true

/-- info: o26 = 2 : ZZ -/
#guard_msgs in
if true then if false then 1 else 2

#guard_msgs in
if false then if true then 1 else 2

/-- info: o28 = 3 : ZZ -/
#guard_msgs in
if false then if true then 1 else 2 else 3

/-- info: o29 = 9 : ZZ -/
#guard_msgs in
if (seen = 8; seen > 0) then seen + 1 else 1/0

/-- info: o30 = 8 : ZZ -/
#guard_msgs in
seen

-- A block returns its final expression. An internal trailing semicolon returns null.
/-- info: o31 = 11/2 : QQ -/
#guard_msgs in
(x = 10; x = x + 1; x/2)

#guard_msgs in
(x = 12;)

/-- info: o33 = 12 : ZZ -/
#guard_msgs in
x

#guard_msgs in
null

#guard_msgs in
(1; 2;)

#guard_msgs in
if false then null = 3

#guard_msgs in
if true then null

/-- info: o38 = true : Boolean -/
#guard_msgs in
null == null

/-- error: attempted to modify a protected symbol 'null' -/
#guard_msgs in
null = 3

/-- error: expected a Boolean condition, got ZZ -/
#guard_msgs in
if 0 then 1 else 2

/-- error: no method for operator and applied to objects of class Boolean, ZZ -/
#guard_msgs in
true and 7

/-- error: no method for operator not applied to objects of class Nothing -/
#guard_msgs in
not null

-- The existing interpreter contract is transactional PER INPUT.
/-- error: division by zero -/
#guard_msgs in
if true then (x = 99; 1/0) else 0

/-- info: o44 = 12 : ZZ -/
#guard_msgs in
x

/-- error: division by zero -/
#guard_msgs in
true and (x = 99; 1/0)

/-- info: o46 = 12 : ZZ -/
#guard_msgs in
x

-- Predicates ignore newlines. Each arm starts after its branch keyword.
/-- info: o47 = 13 : ZZ -/
#guard_msgs in
if
  x > 0
then
  x + 1

/-- info: o48 = 14 : ZZ -/
#guard_msgs in
(if true then
  (x = 14; x)
else
  1/0)

/-- info: o49 = 15 : ZZ -/
#guard_msgs in
if false then 1 else
  (x = 15; x)

/-- info: o50 = true : Boolean -/
#guard_msgs in
true and
  not
    false

-- Whole-word keyword recognition leaves these legal names alone.
/-- info: o51 = 16 : ZZ -/
#guard_msgs in
ifx = 16

/-- info: o52 = 17 : ZZ -/
#guard_msgs in
then$1 = ifx + 1

/-- info: o53 = 17 : ZZ -/
#guard_msgs in
not' = then$1

/-- info: o54 = 17 : ZZ -/
#guard_msgs in
not'

#guard_msgs in
if true then (x = 18; x);

/-- info: o56 = 18 : ZZ -/
#guard_msgs in
x

-- This newline ENDS the conditional, rather than extending its branch with +2.
#guard_msgs in
if false then
  1
/-- info: o58 = 2 : ZZ -/
#guard_msgs in
+2

-- Lean declarations still coexist with the M2 language.
example : Macaulean.M2.run "if true then 7 else 1/0" = .ok (.zz 7) := by decide +kernel

/-- info: o59 = 20 : ZZ -/
#guard_msgs in
x + 2

end BranchingWorksheet

namespace BranchingReaderTests
open Lean Elab Command

-- Direct category lowering, AST printing, and native pretty-printing agree.
run_cmd do
  for source in #[
    "if true then 1", "if false then 1 else 2", "if true then if false then 1 else 2",
    "if false then if true then 1 else 2 else 3", "1 + if true then 2 else 3 + 4",
    "not 1 == 1", "true and false and true", "false or true and false",
    "(x = 3; x + 4)", "(1;)", "(1; 2;)", "(x = 1; (x = 2; x))",
    "if\n1 <\n2\nthen\n3", "(if true then 1\nelse 2)", "true and\nnot false",
    "if true then (x = 1; -- λ, 中文\n x) else 0", "if true then 1;",
    -- Adjacency across a parenthesized newline is now application, not a semicolon.
    "(x = 1\nx + 2)"
  ] do
    let .ok stx := Parser.runParserCategory (← getEnv) `m2 source
      | throwError "category rejected {repr source}"
    let .ok (term, silent) := Macaulean.M2.DSL.lowerInput ⟨stx⟩
      | throwError "lowering rejected {repr source}"
    unless Macaulean.M2.parse source == .ok term do
      throwError "category and string parser differ on {repr source}"
    unless Macaulean.M2.parse term.toM2String == .ok term do
      throwError "AST printing changed {repr source} into {repr term.toM2String}"
    let rendered := (← liftCoreM <| PrettyPrinter.ppCategory `m2 stx).pretty
    let .ok printed := Parser.runParserCategory (← getEnv) `m2 rendered
      | throwError "formatter broke {repr source}: {repr rendered}"
    unless Macaulean.M2.DSL.lowerInput ⟨printed⟩ == .ok (term, silent) do
      throwError "formatting changed the AST or suppressed-output flag"

-- Reader boundary: the next command belongs to Lean's command loop, not to the if.
run_cmd do
  for (source, expected) in #[
    ("if true then 1\nelse 2", "if true then 1\n"),
    ("if\ntrue\nthen\n1\n2", "if\ntrue\nthen\n1\n"),
    ("if true then (1; 2); 3", "if true then (1; 2);"),
    ("if true then 1\r\n+2", "if true then 1\r\n")
  ] do
    let .ok parsed := Macaulean.M2.Input.parse source | throwError "reader failed"
    let consumed := String.Pos.Raw.extract source ⟨0⟩ ⟨parsed.tokens.stop⟩
    unless consumed == expected do throwError "wrong input boundary: {repr consumed}"

-- Both branches must parse even when one will not execute.
run_cmd do
  for source in #["if true then 1 else (1 +)", "if true then 1 else (2 = 3)",
    "if = 3", "then = 3", "else = 3", "and = 3", "or = 3", "not = 3",
    "if true then", "if true then 1 else", "(1;;)"] do
    if (Macaulean.M2.Input.parse source).isOk then
      throwError "accepted malformed input {repr source}"

-- Source positions survive comments, Unicode, and the extra control-flow nodes.
run_cmd do
  let source := "if true then (x = 1; -- λ, 中文\n x) else 0"
  let .ok stx := Parser.runParserCategory (← getEnv) `m2 source
    | throwError "parser failed"
  let body := stx[0][0]
  unless body.getKind == `Macaulean.M2.DSL.ifElse do throwError "conditional is opaque"
  for (token, expected) in #[(body[0], "if"), (body[2], "then"), (body[4], "else")] do
    let some start := token.getPos? | throwError "keyword has no position"
    let some stop := token.getTailPos? | throwError "keyword has no end position"
    unless String.Pos.Raw.extract source start stop == expected do
      throwError "incorrect original keyword range"
  unless body[3][1].getKind == `Macaulean.M2.DSL.seq do throwError "block is opaque"

-- Null results are absent from output history, not stored as fabricated oN values.
run_cmd do
  let original ← getEnv
  let old := Macaulean.M2.DSL.sessionExt.getState original
  let .ok term := Macaulean.M2.parse "(snapshot = 7;)" | throwError "parser failed"
  let result := old.step term
  unless result.output.isNone && result.session.outputs.length == old.outputs.length do
    throwError "null created an output-history entry"
  unless result.session.nextInput == old.nextInput + 1 do throwError "null lost an input number"
  unless result.session.env.lookup "snapshot" == some (.zz 7) do throwError "null lost assignment"
  let saved := Macaulean.M2.DSL.sessionExt.setState original result.session
  let .ok edited := Macaulean.M2.parse "if true then (snapshot = 19;)" | throwError "parser failed"
  let afterEdit := Macaulean.M2.DSL.sessionExt.setState original (old.step edited).session
  unless (Macaulean.M2.DSL.sessionExt.getState saved).env.lookup "snapshot" == some (.zz 7) do
    throwError "old snapshot was mutated"
  unless (Macaulean.M2.DSL.sessionExt.getState afterEdit).env.lookup "snapshot" == some (.zz 19) do
    throwError "edited branch did not recompute"

run_cmd do
  if (Parser.runParserCategory (← getEnv) `command "if true then 1").isOk then
    throwError "conditional command syntax leaked out of the namespace"

end BranchingReaderTests
