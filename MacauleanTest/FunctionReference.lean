import Macaulean.Interpreter.Check
import Macaulean.Interpreter.Input
import Macaulean.Interpreter.Session
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
  ("(f=()->(x:=local x;x==local x);f())", .bool true)
]

example : (edgeValues.all fun (src,v) => run src == .ok v) = true := by decide +kernel

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

-- Discard a successfully compiled function BEFORE serializing the observation.
-- Otherwise an unsupported FunctionClosure wire value could be mistaken for a
-- syntax/binding error and make every malformed-parameter test pass spuriously.
run_cmd do
  let mut checked := 0
  for src in FunctionCases.invalidSyntax do
    let quoted := (Json.str src).compress
    let probe := s!"try (value {quoted}; true) else false"
    match ← queryM2 probe with
    | .ok (.ok (.bool false)) => checked := checked + 1
    | .ok (.ok (.bool true)) => logError m!"native M2 accepted supposedly invalid function syntax {repr src}"
    | .ok reply => logError m!"invalid native syntax-control reply for {repr src}: {reply.toM2String}"
    | .error message => logError m!"native syntax-control query failed: {message}"
  unless checked == FunctionCases.invalidSyntax.length do
    throwError "only {checked}/{FunctionCases.invalidSyntax.length} native syntax/binder controls passed"
  logInfo m!"FUNCTION_INVALID_SYNTAX_COMPLETE: {checked} independent rejection controls"

end Macaulean.M2.FunctionReference
