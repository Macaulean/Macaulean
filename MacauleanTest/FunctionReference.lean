import Macaulean.Interpreter.Check
import Macaulean.Interpreter.Input
import Macaulean.Interpreter.Session
import Macaulean.Interpreter.DSL
import MacauleanTest.FunctionCases

/-! Focused reference and incremental-session regressions. -/
namespace Macaulean.M2.FunctionReference
open Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

example : (parse "{1}=2").isOk = false := by decide +kernel
example : (parse "{x}=2").isOk = false := by decide +kernel
example : (parse "2=3").isOk = false := by decide +kernel
example : (parse "(x,1)=(2,3)").isOk = false := by decide +kernel
example : (parse "(x,y)=(2,3)").isOk = true := by decide +kernel
example : (parse "(x)=2").isOk = true := by decide +kernel
example : (parse "({1}#0)=2").isOk = true := by decide +kernel

example : run "make=n->()->(n=n+1);counter=make 0;(counter(),counter())" =
    .ok (.sequence [.zz 1, .zz 2]) := by decide +kernel

def stepSource (s : Session) (src : String) : Session.Result :=
  match parse src with
  | .ok term => s.step term
  | .error _ => { session := s, outcome := .error .invalidReference, output := none }

run_cmd do
  let built := stepSource {} "make=n->()->(n=n+1);counter=make 0"
  let a := stepSource built.session "counter()"
  let b := stepSource a.session "counter()"
  unless a.outcome == .ok (.zz 1) && b.outcome == .ok (.zz 2) do
    throwError "incremental factory: setup={repr built.outcome}, first={repr a.outcome}, second={repr b.outcome}; env={repr built.session.env}; cells={repr built.session.heap.cells}; functions={repr built.session.heap.functions}"

-- These expectations are literal data, checked both in the kernel and natively.
-- They exercise binding identity, not only the values of ordinary arithmetic.
private def edgeValues : List (String × Value) := [
  ("((true)->true)7", .zz 7),
  ("(f=()->(true:=7;true);f())", .zz 7),
  ("(f=()->(null:=5;null);f())", .zz 5),
  ("(x:=10;f=()->(local x;x=3;x);(f(),x))", .sequence [.zz 3,.zz 10]),
  ("(f=x->(local x;x);f 7)", .zz 7),
  ("(x:=2;f=()->x;x:=3;g=()->x;x=4;(f(),g()))", .sequence [.zz 2,.zz 4]),
  ("(g=()->11;f=()->(h:=()->g();g:=()->99;h());f())", .zz 11),
  ("(mk=x->()->x;f=mk 7;g=x->f();g 99)", .zz 7),
  ("(mk=n->(return ()->n;1/0);f=mk 7;f())", .zz 7),
  ("(x=0;f=y->(x=99;y);g=()->f(return 7);(g(),x))", .sequence [.zz 7,.zz 0]),
  ("(g=()->(return 7)(1/0);g())", .zz 7),
  ("(f=(x,y)->((x,y)=(y,x);(x,y));f(2,3))", .sequence [.zz 3,.zz 2]),
  ("(f=(x,y)->((x,y):=(y,x);(x,y));f(2,3))", .sequence [.null,.null]),
  ("(f=x->x+1;g=()->{f};(g())#0 4)", .zz 5),
  ("(f=n->(x->x+n);g=n->2*n;h=f@@g;(h 3)4)", .zz 10),
  ("(x=1;f=()->(x=(x:=2);x);(f(),x))", .sequence [.zz 2,.zz 2]),
  ("(mk=n->(get:=()->n;put:=x->(n=x;return get);put);f=mk 0;g=f 9;g())", .zz 9),
  ("(local x;a:=local x;x:=7;b:=local x;a==b)", .bool false),
  ("(mk=()->local x;a=mk();b=mk();a==b)", .bool false),
  ("(f=()->(x:=local x;x==local x);f())", .bool true),
  -- Native fixed-arity binding accepts braces, not just parentheses.
  ("({x}->x)(1:7)", .zz 7),
  ("({x}->x){1,2}", .list [.zz 1,.zz 2]),
  ("({x,y}->x+y)(2,3)", .zz 5),
  ("({}->7)()", .zz 7),
  ("(mk={n}->{}->(n=n+1);f=mk 7;(f(),f()))", .sequence [.zz 8,.zz 9]),
  ("(f={x,y}->(z:=x+y;return z;1/0);f(5,6))", .zz 11)
]

example : (edgeValues.all fun (src,v) => run src == .ok v) = true := by decide +kernel
example : parse "{x}->x" = .ok (.lambda (.fixed ["x"]) (.var "x")) := by decide +kernel
example : parse "{}->7" = .ok (.lambda (.fixed []) (.int 7)) := by decide +kernel
example : run "({x,y}->x+y){2,3}" = .error (.arity 2 1) := by decide +kernel

run_cmd do
  let mut checked := 0
  for (src,expected) in edgeValues do
    match ← queryM2 src with
    | .ok (.ok value) =>
      if value == expected then checked := checked + 1
      else logError m!"native lexical edge case {repr src}: {repr value} instead of {repr expected}"
    | .ok .error => logError m!"native M2 rejected lexical edge case {repr src}"
    | .error message => logError m!"native query failed for {repr src}: {message}"
  unless checked == edgeValues.length do
    throwError "only {checked}/{edgeValues.length} lexical edge cases passed natively"
  logInfo m!"FUNCTION_LEXICAL_EDGES_COMPLETE: {checked} explicit typed cases"

-- Check parsing as well as binding: `value` alone may return after a parser
-- failure. Discard valid function results before observing the Boolean, so an
-- unsupported FunctionClosure wire class cannot masquerade as a binding error.
run_cmd do
  let mut checked := 0
  for src in FunctionCases.invalidSyntax do
    let quoted := (Json.str src).compress
    let probe := s!"try (#(parse {quoted}) > 0 and (value {quoted}; true)) else false"
    match ← queryM2 probe with
    | .ok (.ok (.bool false)) => checked := checked + 1
    | .ok (.ok (.bool true)) => logError m!"native M2 accepted supposedly invalid function syntax {repr src}"
    | .ok reply => logError m!"invalid native syntax-control reply for {repr src}: {reply.toM2String}"
    | .error message => logError m!"native syntax-control query failed: {message}"
  unless checked == FunctionCases.invalidSyntax.length do
    throwError "only {checked}/{FunctionCases.invalidSyntax.length} native syntax/binder controls passed"
  logInfo m!"FUNCTION_INVALID_SYNTAX_COMPLETE: {checked} independent rejection controls"

-- The editor adapter must recognize exactly the same parameter convention, and
-- preserve braces in its native formatter while the AST printer may normalize.
run_cmd do
  for src in #["{x}->x", "{}->7", "{x,y}->x+y", "({x}->x)(1:7)",
      "{x, -- λ, 中文\n y}->x+y", "f={x}->x;", "{n}->{}->n"] do
    let .ok stx := Lean.Parser.runParserCategory (← getEnv) `m2 src
      | throwError "brace-parameter category parser failed for {repr src}"
    let .ok (term,silent) := DSL.lowerInput ⟨stx⟩
      | throwError "brace-parameter lowering failed for {repr src}"
    unless parse src == .ok term do throwError "brace-parameter AST mismatch"
    unless parse term.toM2String == .ok term do throwError "brace-parameter AST printing mismatch"
    let rendered := (← liftCoreM <| PrettyPrinter.ppCategory `m2 stx).pretty
    let .ok printed := Lean.Parser.runParserCategory (← getEnv) `m2 rendered
      | throwError "brace-parameter formatting failed"
    unless DSL.lowerInput ⟨printed⟩ == .ok (term,silent) do
      throwError "brace-parameter formatting changed arity or body"

end Macaulean.M2.FunctionReference
