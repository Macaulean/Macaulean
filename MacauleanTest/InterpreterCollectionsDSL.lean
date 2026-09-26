import Macaulean.Interpreter.DSL
import MacauleanTest.CollectionCases

/-!
# An immutable M2 notebook

Open in Lean and inspect the ordinary InfoView messages. This is bare Macaulay2,
not string literals or quoted terms. All expected outputs are executable tests.
-/
namespace CollectionWorksheet
open M2

/-- info: o1 = {} : List -/
#guard_msgs in
{}

/-- info: o2 = () : Sequence -/
#guard_msgs in
()

-- Null is silent, but empty collections above are actual outputs.
#guard_msgs in
null

/-- info: o4 = {7} : List -/
#guard_msgs in
{7}

/-- info: o5 = 7 : ZZ -/
#guard_msgs in
(7)

/-- info: o6 = 1:(7) : Sequence -/
#guard_msgs in
1:7

/-- info: o7 = (1, null) : Sequence -/
#guard_msgs in
(1,)

/-- info: o8 = (null, 1) : Sequence -/
#guard_msgs in
(,1)

/-- info: o9 = {null, null} : List -/
#guard_msgs in
{,}

/-- info: o10 = (1, 2, 3) : Sequence -/
#guard_msgs in
1,2,3

/-- info: o11 = ((1, 2), 3) : Sequence -/
#guard_msgs in
((1,2),3)

/-- info: o12 = {(1, 2, 3)} : List -/
#guard_msgs in
{1..3}

/-- info: o13 = {(), {}, {1, (2, 3)}} : List -/
#guard_msgs in
{(),{}, {1,(2,3)}}

/-- info: o14 = {1/1, 2/3, true, null} : List -/
#guard_msgs in
{1/1,2/3,true,null}

/-- info: o15 = 3 : ZZ -/
#guard_msgs in
#{10,20,30}

/-- info: o16 = 2 : ZZ -/
#guard_msgs in
#(1,)

/-- info: o17 = 1 : ZZ -/
#guard_msgs in
#{1..3}

/-- info: o18 = 3 : ZZ -/
#guard_msgs in
#(1..3)

/-- info: o19 = 2 : ZZ -/
#guard_msgs in
#{{1,2},{3}}#0

-- Assignments persist, but collection contents cannot be changed.
#guard_msgs in
xs = {10,20,30};
#guard_msgs in
saved = xs;

/-- info: o22 = 10 : ZZ -/
#guard_msgs in
xs#0

/-- info: o23 = 30 : ZZ -/
#guard_msgs in
xs#-1

/-- info: o24 = 10 : ZZ -/
#guard_msgs in
xs#-3

/-- info: o25 = true : Boolean -/
#guard_msgs in
xs#?(-3)

/-- info: o26 = false : Boolean -/
#guard_msgs in
xs#?(-4)

/-- info: o27 = false : Boolean -/
#guard_msgs in
xs#?3

/-- error: index 3 out of bounds for collection of length 3 -/
#guard_msgs in
xs#3

/-- error: cannot modify immutable List -/
#guard_msgs in
xs#0 = 99

/-- info: o30 = {10, 20, 30} : List -/
#guard_msgs in
saved

/-- info: o31 = {10, 20, 30, 40} : List -/
#guard_msgs in
xs = xs | {40}

/-- info: o32 = {10, 20, 30} : List -/
#guard_msgs in
saved

/-- info: o33 = (1, 2, 3, 4) : Sequence -/
#guard_msgs in
(1,2)|(3,4)

/-- info: o34 = (-2, -1, 0, 1) : Sequence -/
#guard_msgs in
(-2)..1

/-- info: o35 = (-2, -1, 0) : Sequence -/
#guard_msgs in
(-2)..<1

/-- info: o36 = () : Sequence -/
#guard_msgs in
5..2

/-- info: o37 = 1:(5) : Sequence -/
#guard_msgs in
5..5

/-- info: o38 = (7, 7, 7) : Sequence -/
#guard_msgs in
3:7

/-- info: o39 = ((1, 2), (1, 2)) : Sequence -/
#guard_msgs in
2:(1,2)

#guard_msgs in
counter = 0;

-- Elements run left to right, threading assignments through nested collections.
/-- info: o41 = {1, 2, 2} : List -/
#guard_msgs in
{(counter=counter+1), (counter=counter+1), counter}

/-- info: o42 = (3, 3, 3) : Sequence -/
#guard_msgs in
3:(counter=counter+1)

/-- info: o43 = () : Sequence -/
#guard_msgs in
0:(counter=counter+1)

/-- info: o44 = 4 : ZZ -/
#guard_msgs in
counter

/-- error: division by zero -/
#guard_msgs in
0:(1/0)

-- Short-circuiting, unlike repetition, really skips its operand.
/-- info: o46 = false : Boolean -/
#guard_msgs in
false and {}#0

/-- info: o47 = {5/6, (7, 8)} : List -/
#guard_msgs in
if true then {1/2+1/3,(7,8)} else {1/0}

/-- info: o48 = {2} : List -/
#guard_msgs in
{1;2}

/-- info: o49 = {null} : List -/
#guard_msgs in
{1;}

#guard_msgs in
({1,2};)

/-- info: o51 = true : Boolean -/
#guard_msgs in
{{1,(2,3)}} == {{1/1,(2,3/1)}}

/-- info: o52 = false : Boolean -/
#guard_msgs in
{1} != {1/1}

/-- info: o53 = false : Boolean -/
#guard_msgs in
{0,true} == {1,7}

/-- error: no method for operator == applied to objects of class Boolean, ZZ -/
#guard_msgs in
{true} == {1}

/-- error: no method for operator # applied to objects of class List, QQ -/
#guard_msgs in
xs#(1/1)

/-- info: o56 = {1, 2, 3} : List -/
#guard_msgs in
{1,
 2, -- UTF-8 source positions: λ, 中文
 3}

/-- info: o57 = (1, 2, 3) : Sequence -/
#guard_msgs in
(1,
 2,
 3)

-- Multiple inputs on the same physical line remain separate snapshots.
left = {1}; right = (2,3);

/-- info: o60 = 3 : ZZ -/
#guard_msgs in
#left + #right

-- Failed collection construction is transactional just like other inputs.
/-- error: division by zero -/
#guard_msgs in
{(counter=99),1/0}

/-- info: o62 = 4 : ZZ -/
#guard_msgs in
counter

example : Macaulean.M2.run "{1}#0" = .ok (.zz 1) := by decide +kernel

/-- info: o63 = 40 : ZZ -/
#guard_msgs in
xs#-1

end CollectionWorksheet

namespace CollectionReaderTests
open Lean Elab Command
open Macaulean.M2 (Value Term)

run_cmd do
  for source in #[
    "{}", "()", "{1}", "(1,)", "(,)", "1,2,3", "((1,2),3)", "{(1,2)}",
    "{1..3}", "{1,,3}", "{1;}", "(1;2,3)", "if true then {1} else (2,3)",
    "#{1,2}", "{1}#0", "{1}#?(-1)", "(1,2)|(3,4)", "2:(1,2)",
    "{1, -- λ, 中文\n2}", "{1,2};", "cp=1,2", "{1}#0=3"
  ] do
    let .ok stx := Parser.runParserCategory (← getEnv) `m2 source
      | throwError "category rejected {repr source}"
    let .ok (term, silent) := Macaulean.M2.DSL.lowerInput ⟨stx⟩
      | throwError "lowering rejected {repr source}"
    unless Macaulean.M2.parse source == .ok term do throwError "shared-parser disagreement: {repr source}"
    unless Macaulean.M2.parse term.toM2String == .ok term do
      throwError "AST printing changed {repr source} to {repr term.toM2String}"
    let rendered := (← liftCoreM <| PrettyPrinter.ppCategory `m2 stx).pretty
    let .ok printed := Parser.runParserCategory (← getEnv) `m2 rendered
      | throwError "formatter broke {repr source}: {repr rendered}"
    unless Macaulean.M2.DSL.lowerInput ⟨printed⟩ == .ok (term, silent) do
      throwError "formatting changed nesting, AST, or output suppression"

-- All successful values, including nested singleton sequences, must print back
-- to the same typed value, independently of how their expressions were written.
run_cmd do
  for (_, value) in Macaulean.M2.CollectionCases.successes do
    unless Macaulean.M2.run value.toM2String == .ok value do
      throwError "value printer changed the typed value {repr value}"

run_cmd do
  for source in Macaulean.M2.CollectionCases.invalidSyntax do
    if (Macaulean.M2.Input.parse source).isOk then throwError "reader accepted {repr source}"

-- Closing braces and parentheses match, and collection newlines do not absorb
-- the following Lean command. Commas at top level have optional right operands.
run_cmd do
  for (source, expected) in #[
    ("{1,\n2}\n3", "{1,\n2}\n"),
    ("(1,\n2);3", "(1,\n2);"),
    ("1,\n2", "1,\n"),
    ("{1,\r\n2}\r\n+3", "{1,\r\n2}\r\n")
  ] do
    let .ok parsed := Macaulean.M2.Input.parse source | throwError "input reader failed"
    unless String.Pos.Raw.extract source ⟨0⟩ ⟨parsed.tokens.stop⟩ == expected do
      throwError "incorrect collection input boundary for {repr source}"

-- Native syntax nodes retain delimiters and original UTF-8 byte locations.
run_cmd do
  let source := "{1, -- λ, 中文\n (2,3)}"
  let .ok stx := Parser.runParserCategory (← getEnv) `m2 source | throwError "parser failed"
  let body := stx[0][0]
  unless body.getKind == `Macaulean.M2.DSL.listBody do throwError "list syntax is opaque"
  unless body[1].getKind == `Macaulean.M2.DSL.comma do throwError "comma syntax is opaque"
  for (token, expected) in #[(body[0], "{"), (body[2], "}"),
      (body[1][1], ","), (body[1][2][0], "("), (body[1][2][2], ")")] do
    let some start := token.getPos? | throwError "missing source position"
    let some stop := token.getTailPos? | throwError "missing source end"
    unless String.Pos.Raw.extract source start stop == expected do throwError "corrupt collection source range"

-- Old snapshots and aliases preserve the same immutable value after rebinding.
run_cmd do
  let original ← getEnv
  let old := Macaulean.M2.DSL.sessionExt.getState original
  let .ok init := Macaulean.M2.parse "snapshot={1,(2,3)}; alias=snapshot" | throwError "parser failed"
  let stored := old.step init
  let saved := Macaulean.M2.DSL.sessionExt.setState original stored.session
  let .ok edit := Macaulean.M2.parse "snapshot={9}" | throwError "parser failed"
  let edited := stored.session.step edit
  let expected := Value.list [.zz 1, .sequence [.zz 2, .zz 3]]
  unless edited.session.env.lookup "alias" == some expected do throwError "rebinding mutated an alias"
  unless (Macaulean.M2.DSL.sessionExt.getState saved).env.lookup "snapshot" == some expected do
    throwError "rebinding mutated an old snapshot"
  let .ok mutation := Macaulean.M2.parse "snapshot#0=99" | throwError "parser failed"
  let refused := edited.session.step mutation
  unless refused.outcome.isError && refused.session.env == edited.session.env do
    throwError "indexed assignment changed immutable state"
  for term in [Term.listLit [], Term.sequence []] do
    let result := old.step term
    unless result.output.isSome do throwError "empty collection was mistaken for null"

run_cmd do
  if (Parser.runParserCategory (← getEnv) `command "{1,2}").isOk then
    throwError "collection command syntax leaked from its namespace"

end CollectionReaderTests
