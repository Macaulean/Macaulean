import MacauleanTest.FunctionCases
import Macaulean.Interpreter.Wire
import Macaulean.Interpreter.Session

/-! Kernel checks for the actual source runtime, including lexical resolution.
No `native_decide`, axioms, or proof holes are used. -/
namespace Macaulean.M2.FunctionTests
open FunctionCases
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

example : (successes.all fun (src,v) => run src == .ok v) = true := by decide +kernel
example : (errors.all fun (src,e) => run src == .error e) = true := by decide +kernel

private def syntaxError (s : String) : Bool :=
  match parse s with | .error _ => true | _ => false
example : invalidSyntax.all syntaxError = true := by decide +kernel

-- Parameter parentheses survive parsing; they are not ordinary grouping here.
example : parse "x -> x" = .ok (.lambda (.variadic "x") (.var "x")) := by decide +kernel
example : parse "(x) -> x" = .ok (.lambda (.fixed ["x"]) (.var "x")) := by decide +kernel
example : parse "()->7" = .ok (.lambda (.fixed []) (.int 7)) := by decide +kernel
example : parse "f g 3" = .ok (.apply (.var "f") (.apply (.var "g") (.int 3))) := by decide +kernel
example : parse "f(3)^2" = .ok (.apply (.var "f") (.binop .pow (.int 3) (.int 2))) := by decide +kernel
example : parse "f=x->y->x+y" = .ok (.assign "f" (.lambda (.variadic "x")
    (.lambda (.variadic "y") (.binop .add (.var "x") (.var "y"))))) := by decide +kernel
example : parse "(x,y):=(2,3)" = .ok (.assignMany true ["x","y"] (.sequence [.int 2,.int 3])) := by decide +kernel
example : parse "return 1,2" = .ok (.sequence [.returnTerm (.int 1), .int 2]) := by decide +kernel

-- Recursion is explicit and bounded; exhausted computations are never successes.
example : runWithFuel 32 "f=x->f x;f 0" = .error .fuelExhausted := by decide +kernel
example : runWithFuel 0 "7" = .error .fuelExhausted := by decide +kernel
example : runWithFuel 64 "f=n->if n==0 then 1 else n*f(n-1);f 5" = .ok (.zz 120) := by decide +kernel

-- The return expression of local is a symbol, not a write to the local cell.
example : run "local x" = .ok (.symbol "x" 0) := by decide +kernel
example : run "local x;x" = .ok .null := by decide +kernel
example : run "x:=local y;x==x" = .ok (.bool true) := by decide +kernel

-- The native value decoder must never admit forged session-relative handles.
example : (Value.ofWire ["FunctionClosure", "0"]).isOk = false := by decide +kernel
example : (Value.ofWire ["Symbol", "x", "0"]).isOk = false := by decide +kernel
example : (Value.ofWire ["List", "1", "FunctionClosure", "0"]).isOk = false := by decide +kernel

-- A captured cell is shared by sibling closures and preserved by old snapshots.
private def execute (s : Session) (src : String) : Session.Result :=
  match parse src with
  | .ok term => s.step term
  | .error _ => ⟨s, .error .invalidReference, none, []⟩
private def initial : Session :=
  (execute {} "mk=()->(p:=0;(()->(p=p+1),()->p));fs=mk()").session
private def advanced : Session := (execute initial "(fs#0)()").session
example : (execute initial "(fs#1)()").outcome = .ok (.zz 0) := by decide +kernel
example : (execute advanced "(fs#1)()").outcome = .ok (.zz 1) := by decide +kernel
private def failed : Session := (execute advanced "((fs#0)();1/0)").session
example : (execute failed "(fs#1)()").outcome = .ok (.zz 1) := by decide +kernel

-- File locals survive successive commands and can shadow global bindings.
private def locals : Session := (execute {} "x=10;f=()->x;x:=20;g=()->x").session
example : (execute locals "(f(),g(),x)").outcome = .ok (.sequence [.zz 10,.zz 20,.zz 20]) := by decide +kernel
end Macaulean.M2.FunctionTests
