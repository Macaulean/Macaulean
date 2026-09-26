import Macaulean.Interpreter.Check

/-! Native reference observations for the function/lexical-binding extension.
These probes run independently of the Lean implementation. -/
namespace Macaulean.M2.FunctionReference
open Lean Elab Command
run_cmd do
  for s in #[
    "(f = x -> x; f())",
    "(f = x -> x; f(1,2))",
    "(f = (x) -> x; f(1,2))",
    "(f = (x) -> x; f())",
    "(f = (x) -> x; f(1:7))",
    "(f = x -> x; f(1:7))",
    "(f = () -> 7; f 1)",
    "(f = () -> 7; f())",
    "(f = (x,y) -> x+y; f {1,2})",
    "(f = (x,x) -> x; f(1,2))",
    "(f = ((x,y)) -> x+y; f(1,2))",
    "(x=100; f=() -> (x := x+1; x); f())",
    "(x=100; f=() -> (y=x; x:=9; y); f())",
    "(x=100; f=() -> (g=()->x; x:=9; g()); f())",
    "(x=100; f=() -> (if false then x:=9; x); f())",
    "(x=100; f=() -> (false and (x:=9;true); x); f())",
    "(f=()->((a:=7);a); f())",
    "(f=()->({a:=7};a); f())",
    "(f=()->(x:=2; g=()->x; x:=3; g()); f())",
    "(f=()->(local x; x); f())",
    "(f=()->(local x; x=7; x); f())",
    "(f=()->(g:=n->if n==0 then 1 else n*g(n-1); g 5); f())",
    "(f=()->(local g; g=n->if n==0 then 1 else n*g(n-1); g 5); f())",
    "(x=10; f=()->x; x=20; f())",
    "(x=10; f=()->x; g=x->f(); g 99)",
    "(mk=()->(p:=0; (() -> (p=p+1), ()->p)); fs=mk(); (fs#0)(); (fs#1)())",
    "(f=x->(return x+1;1/0); f 6)",
    "(f=x->(return;1/0); f 6)",
    "(f=x->(return 1,2;1/0); f 6)",
    "(f=x->(return (1,2);1/0); f 6)",
    "return 7",
    "(f=()->(g=()->return 3; g()+4); f())",
    "(x=2; y=3; (x,y)=(y,x); (x,y))",
    "((x,y):=(2,3); x+y)",
    "((x,y)=(2); x+y)",
    "((x,y)={2,3}; x+y)",
    "(f=x->x+1; g=x->2*x; f g 3)",
    "(f=x->x+1; f(3)^2)",
    "(f=x->x+1; f 3^2)",
    "(f=x->x+1; f -3)",
    "(f=x->x+1; f(-3))",
    "(f=x->x+1; g=x->2*x; (f@@g) 3)",
    "(f=x->x+1; g=x->2*x; f @ g 3)",
    "(f=x->x>0; g=x->x<5; (f and g) 3)",
    "(f=x->x>0; (not f) 3)",
    "(f=x->x; f==f)",
    "((x->x)==(x->x))",
    "(f=x->x; g=f; f!=g)",
    "(f=x->x+1; {f,f}#0 3)",
    "(f=(x,y)->x+y; f(2,3))"
  ] do
    match ← queryM2 s with
    | .ok r => logInfo m!"FUNCTION_REFERENCE {repr s} => {r.toM2String}"
    | .error e => logInfo m!"FUNCTION_REFERENCE {repr s} => UNSUPPORTED {e}"
end Macaulean.M2.FunctionReference
