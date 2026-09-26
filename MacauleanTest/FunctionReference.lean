import Macaulean.Interpreter.Check
import Macaulean.Interpreter.Input
import Macaulean.Interpreter.Session
import MacauleanTest.FunctionCases

/-! Focused reference and incremental-session regressions. -/
namespace Macaulean.M2.FunctionReference
open Lean Elab Command

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

end Macaulean.M2.FunctionReference
