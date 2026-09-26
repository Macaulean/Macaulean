import Macaulean.Interpreter.DSL
import MacauleanTest.FunctionCases

/-!
# Functions are values; bindings are not copies

An executable M2 worksheet. Open it in Lean and move through the inputs: the
InfoView is the output pane. Every expected value, error, warning, and intentional
silence below is checked during elaboration. No native M2 process is involved.
-/
namespace FunctionWorksheet
open M2

-- Calling conventions and actual M2 application precedence.
#guard_msgs in
square = x -> x^2;

/-- info: o2 = 144 : ZZ -/
#guard_msgs in
square 12

#guard_msgs in
bump = x -> x + 1;

/-- info: o4 = 10 : ZZ -/
#guard_msgs in
bump(3)^2

/-- info: o5 = 16 : ZZ -/
#guard_msgs in
(bump 3)^2

#guard_msgs in
identity = x -> x;

/-- info: o7 = () : Sequence -/
#guard_msgs in
identity()

/-- info: o8 = (1, 2) : Sequence -/
#guard_msgs in
identity(1,2)

#guard_msgs in
one = (x) -> x;

/-- info: o10 = 7 : ZZ -/
#guard_msgs in
one(1:7)

/-- error: expected 1 arguments, got 2 -/
#guard_msgs in
one(1,2)

/-- error: expected 1 arguments, got 0 -/
#guard_msgs in
one()

#guard_msgs in
constant = () -> 7;

/-- info: o14 = 7 : ZZ -/
#guard_msgs in
constant()

/-- error: expected 0 arguments, got 1 -/
#guard_msgs in
constant 1

#guard_msgs in
add = (x,y) -> x+y;

/-- info: o17 = 5 : ZZ -/
#guard_msgs in
add(2,3)

/-- error: expected 2 arguments, got 1 -/
#guard_msgs in
add {2,3}

-- Functions as arguments, return values, and composition.
#guard_msgs in
twice = (f,x) -> f(f x);

/-- info: o20 = 9 : ZZ -/
#guard_msgs in
twice(bump,7)

#guard_msgs in
compose = (f,g) -> x -> f(g x);
#guard_msgs in
double = x -> 2*x;
#guard_msgs in
composed = compose(bump,double);

/-- info: o24 = 7 : ZZ -/
#guard_msgs in
composed 3

/-- info: o25 = 7 : ZZ -/
#guard_msgs in
(bump@@double)3

/-- info: o26 = 8 : ZZ -/
#guard_msgs in
(double@@bump)3

-- Global references are not dynamically rebound by callers.
#guard_msgs in
x = 100;
#guard_msgs in
capture = () -> x;

/-- info: o29 = 100 : ZZ -/
#guard_msgs in
(x -> capture())9

#guard_msgs in
x = 200;

/-- info: o31 = 200 : ZZ -/
#guard_msgs in
capture()

-- File locals survive later inputs; earlier references retain their bindings.
#guard_msgs in
x := 7;
#guard_msgs in
readLocal = () -> x;
#guard_msgs in
x = 8;

/-- info: o35 = 8 : ZZ -/
#guard_msgs in
readLocal()

/-- info: o36 = 200 : ZZ -/
#guard_msgs in
capture()

/-- warning: redeclaration of local variable 'x' -/
#guard_msgs in
x := 11;

/-- info: o38 = 8 : ZZ -/
#guard_msgs in
readLocal()

/-- info: o39 = 11 : ZZ -/
#guard_msgs in
x

-- Factory calls allocate independent cells; aliases share the same closure.
#guard_msgs in
makeCounter = start -> (n := start; () -> (n = n+1));
#guard_msgs in
ca = makeCounter 0;
#guard_msgs in
cb = makeCounter 100;

/-- info: o43 = 1 : ZZ -/
#guard_msgs in
ca()

/-- info: o44 = 2 : ZZ -/
#guard_msgs in
ca()

/-- info: o45 = 101 : ZZ -/
#guard_msgs in
cb()

#guard_msgs in
alias = ca;

/-- info: o47 = 3 : ZZ -/
#guard_msgs in
alias()

/-- info: o48 = 4 : ZZ -/
#guard_msgs in
ca()

-- Sibling closures communicate after their enclosing call has returned.
#guard_msgs in
makePair = () -> (n := 0; (() -> (n=n+1), () -> n));
#guard_msgs in
pair = makePair();

/-- info: o51 = 1 : ZZ -/
#guard_msgs in
(pair#0)()

/-- info: o52 = 1 : ZZ -/
#guard_msgs in
(pair#1)()

-- The inherited transaction contract now includes captured cells as well.
/-- error: division by zero -/
#guard_msgs in
((pair#0)(); 1/0)

/-- info: o54 = 1 : ZZ -/
#guard_msgs in
(pair#1)()

-- Recursion, including a self-reference to an escaped local function.
#guard_msgs in
factorial = n -> if n == 0 then 1 else n*factorial(n-1);

/-- info: o56 = 720 : ZZ -/
#guard_msgs in
factorial 6

#guard_msgs in
makeRecursive = () -> (local rec; rec=n->if n==0 then 0 else 1+rec(n-1); rec);
#guard_msgs in
recurse = makeRecursive();

/-- info: o59 = 10 : ZZ -/
#guard_msgs in
recurse 10

-- Return skips arbitrary subsequent code, without escaping an outer call.
#guard_msgs in
early = x -> (if x < 0 then return -x; {x,x^2});

/-- info: o61 = 7 : ZZ -/
#guard_msgs in
early(-7)

/-- info: o62 = {3, 9} : List -/
#guard_msgs in
early 3

#guard_msgs in
nestedReturn = () -> (g := () -> return 3; g()+4);

/-- info: o64 = 7 : ZZ -/
#guard_msgs in
nestedReturn()

-- Multiple return values and simultaneous binding.
#guard_msgs in
powers = n -> (n,n^2,n^3);
#guard_msgs in
(a,b,c) = powers 3;

/-- info: o67 = {3, 9, 27} : List -/
#guard_msgs in
{a,b,c}

-- Function-valued Boolean operations compose predicates lazily.
#guard_msgs in
good = x -> x > 0;
#guard_msgs in
bad = x -> 1/0;

/-- info: o70 = true : Boolean -/
#guard_msgs in
(good or bad)3

/-- info: o71 = false : Boolean -/
#guard_msgs in
((not good) and bad)3

#guard_msgs in
functions = {bump,double,square};

/-- info: o73 = 81 : ZZ -/
#guard_msgs in
functions#2 9

-- Divergence is bounded, reported, and does not destroy the worksheet.
#guard_msgs in
divergent = x -> divergent x;

/-- error: M2 evaluation depth exhausted -/
#guard_msgs in
set_option m2.maxDepth 64 in
divergent 0

/-- info: o76 = 25 : ZZ -/
#guard_msgs in
square 5

#guard_msgs in
uninitialized = () -> (if false then z:=9; z);
#guard_msgs in
uninitialized()

/-- info: o79 = 1/4 : QQ -/
#guard_msgs in
square(1/2)

-- This Lean x is unrelated to the file-local M2 x.
def x : Nat := 999
example : x = 999 := rfl

/-- info: o80 = 11 : ZZ -/
#guard_msgs in
x

end FunctionWorksheet

namespace FunctionReaderTests
open Lean Elab Command

run_cmd do
  for src in #[
    "x->x", "(x)->x", "()->7", "(x,y)->x+y", "x->y->x+y", "f g 3", "f(3)^2",
    "(f 3)^2", "f@@g 3", "f(x,y)", "(x,y):=(2,3)", "local x", "return", "return 1,2",
    "return(1,2)", "f=x->\n x+1;", "(x,y)->(z:=x+y;\nz)", "{x->x,y->y+1}",
    "(x, -- λ, 中文\n y) -> (z := x; z+y)"
  ] do
    let .ok stx := Parser.runParserCategory (← getEnv) `m2 src
      | throwError "category rejected {repr src}"
    let .ok (term,silent) := Macaulean.M2.DSL.lowerInput ⟨stx⟩
      | throwError "lowering rejected {repr src}"
    unless Macaulean.M2.parse src == .ok term do throwError "parser disagreement for {repr src}"
    unless Macaulean.M2.parse term.toM2String == .ok term do
      throwError "AST printer changed {repr src} into {repr term.toM2String}"
    let rendered := (← liftCoreM <| PrettyPrinter.ppCategory `m2 stx).pretty
    let .ok restx := Parser.runParserCategory (← getEnv) `m2 rendered
      | throwError "formatter broke {repr src}"
    unless Macaulean.M2.DSL.lowerInput ⟨restx⟩ == .ok (term,silent) do
      throwError "formatter changed arity, nesting, or suppression"

-- Raw parameter parentheses, arrow, and binding tokens have independent ranges.
run_cmd do
  let src := "(x, -- λ, 中文\n y) -> (z := x; z+y)"
  let .ok stx := Parser.runParserCategory (← getEnv) `m2 src | throwError "parser failed"
  let body := stx[0][0]
  unless body.getKind == `Macaulean.M2.DSL.lambda do throwError "opaque lambda syntax"
  unless body[0].getKind == `Macaulean.M2.DSL.paren do throwError "lost parameter parentheses"
  for (token,expected) in #[(body[0][0],"("),(body[0][2],")"),(body[1],"->"),
      (body[2][1][0][1],":=")] do
    let some a := token.getPos? | throwError "missing function source position"
    let some b := token.getTailPos? | throwError "missing function source end"
    unless String.Pos.Raw.extract src a b == expected do throwError "corrupt UTF-8 token range"

run_cmd do
  for (src,expected) in #[
    ("f=x->\n x+1\n7", "f=x->\n x+1\n"),
    ("local\n x\n7", "local\n x\n"),
    ("return\n7", "return\n"),
    ("f=(x,\ny)->x+y;7", "f=(x,\ny)->x+y;"),
    ("f=x->\r\n x+1\r\n7", "f=x->\r\n x+1\r\n")
  ] do
    let .ok input := Macaulean.M2.Input.parse src | throwError "input boundary failed"
    unless String.Pos.Raw.extract src ⟨0⟩ ⟨input.tokens.stop⟩ == expected do
      throwError "function reader absorbed the next command"

-- Immutable environments are actual REPL checkpoints, including escaped cells.
run_cmd do
  let original ← getEnv
  let runInput := fun (s : Macaulean.M2.Session) (src : String) =>
    match Macaulean.M2.parse src with
    | .ok t => s.step t
    | .error _ => { session := s, outcome := .error .invalidReference, output := none }
  let built := runInput {} "make=n->()->(n=n+1);counter=make 0"
  let saved := Macaulean.M2.DSL.sessionExt.setState original built.session
  let a := runInput built.session "counter()"
  let b := runInput a.session "counter()"
  unless a.outcome == .ok (.zz 1) && b.outcome == .ok (.zz 2) do throwError "captured updates failed"
  let replay := runInput (Macaulean.M2.DSL.sessionExt.getState saved) "counter()"
  unless replay.outcome == .ok (.zz 1) do throwError "a later call mutated an earlier snapshot"
  let bad := runInput b.session "(counter();1/0)"
  let next := runInput bad.session "counter()"
  unless next.outcome == .ok (.zz 3) do throwError "failed input published a captured write"
  let exhausted := match Macaulean.M2.parse "local f;f=x->(counter();f x);f 0" with
    | .ok t => b.session.step t false 32
    | .error _ => b
  unless exhausted.outcome == .error .fuelExhausted do throwError "unbounded recursion accepted"
  unless (runInput exhausted.session "counter()").outcome == .ok (.zz 3) do
    throwError "fuel exhaustion published captured writes"
  let displayed := runInput {} "x->x"
  unless displayed.output.isSome && displayed.outcome == .ok (.closure 0) do
    throwError "functions cannot be displayed as worksheet results"

run_cmd do
  if (Parser.runParserCategory (← getEnv) `command "x -> x").isOk then
    throwError "function syntax leaked outside open M2 scope"

end FunctionReaderTests
