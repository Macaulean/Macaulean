import Macaulean.Interpreter.Run

/-!
# Function and lexical-binding reference corpus

Expected results are explicit data, never computed by the interpreter being
checked. The same corpus is checked in Lean's kernel and against native M2.
Opaque function handles are tested by calling them, not by comparing process IDs.
-/
namespace Macaulean.M2.FunctionCases
open Value

def successes : List (String × Value) := [
  -- Calling conventions, including the significant parameter parentheses.
  ("(f = x -> x; f())", .sequence []),
  ("(f = x -> x; f 7)", .zz 7),
  ("(f = x -> x; f(1,2))", .sequence [.zz 1, .zz 2]),
  ("(f = x -> x; f(1:7))", .sequence [.zz 7]),
  ("(f = (x) -> x; f(1:7))", .zz 7),
  ("(f = (x) -> x; f 7)", .zz 7),
  ("(f = (x) -> x; f {1,2})", .list [.zz 1, .zz 2]),
  ("(f = () -> 7; f())", .zz 7),
  ("(f = (x,y) -> x+y; f(2,3))", .zz 5),
  ("(f = (x,y,z) -> {x,y,z}; f(1,2/3,true))", .list [.zz 1, .qq (mkRat 2 3), .bool true]),
  ("(x -> x^2) 7", .zz 49),
  ("((x,y) -> x/y)(5,6)", .qq (mkRat 5 6)),
  ("(f=x->x; f null)", .null),
  ("(f=()->1/0; 7)", .zz 7),
  -- First-class functions, application association, and precedence.
  ("(f=x->x+1; g=x->2*x; f g 3)", .zz 7),
  ("(f=x->x+1; f(3)^2)", .zz 10),
  ("(f=x->x+1; f 3^2)", .zz 10),
  ("(f=x->x+1; (f 3)^2)", .zz 16),
  ("(f=x->x+1; f(-3))", .zz (-2)),
  ("(f=x->x+1; f 3 * 2)", .zz 8),
  ("(f=x->x+1; {f,f}#0 3)", .zz 4),
  ("(f=x->y->x+y; (f 7) 8)", .zz 15),
  ("(f=x->y->x+y; g=f 3; h=f 10; (g 4,h 4))", .sequence [.zz 7, .zz 14]),
  ("(twice=(f,x)->f(f x); twice(x->x+3,4))", .zz 10),
  ("(comp=(f,g)->x->f(g x); h=comp(x->x+1,x->2*x); h 5)", .zz 11),
  ("(f=x->x+1; g=x->2*x; (f@@g)3)", .zz 7),
  ("(f=x->x+1; g=x->2*x; (g@@f)3)", .zz 8),
  ("(f=x->x+1; g=x->2*x; f@@g 3)", .zz 7),
  ("(f=x->x+1; g=x->2*x; h=x->x-3; (f@@g@@h)5)", .zz 5),
  -- Lexical rather than dynamic scope, and source-ordered declarations.
  ("(x=10; f=()->x; x=20; f())", .zz 20),
  ("(x=10; f=()->x; g=x->f(); g 99)", .zz 10),
  ("(x=100; f=()->(x:=9;x); (f(),x))", .sequence [.zz 9, .zz 100]),
  ("(x=100; f=()->(y=x;x:=9;y); f())", .zz 100),
  ("(x=100; f=()->(g=()->x;x:=9;g()); f())", .zz 100),
  ("(x=100; f=()->(if false then x:=9;x); f())", .null),
  ("(x=100; f=()->(false and (x:=9;true);x); f())", .null),
  ("(f=()->((a:=7);a);f())", .zz 7),
  ("(f=()->({a:=7};a);f())", .zz 7),
  ("(f=()->(x:=2;g=()->x;x:=3;g());f())", .zz 2),
  ("(f=()->(local x;x);f())", .null),
  ("(f=()->(local x;x=7;x);f())", .zz 7),
  ("(f=()->(x:=x;x);f())", .null),
  ("(f=x->(x=x+1;x);x=99;(f 4,x))", .sequence [.zz 5, .zz 99]),
  ("(f=x->(x:=3;x);f 9)", .zz 3),
  ("(x:=4;f=()->x;x=8;f())", .zz 8),
  ("(x:=4;f=()->x;x:=8;f())", .zz 4),
  ("(x=4;f=()->x;x:=8;f())", .zz 4),
  -- Escaping closures share cells, but different factory calls do not.
  ("(mk=()->(p:=0; (()->(p=p+1),()->p));fs=mk();(fs#0)();(fs#1)())", .zz 1),
  ("(mk=()->(p:=0; (()->p,i->p=i));fs=mk();(fs#1)555;(fs#0)())", .zz 555),
  ("(mk=n->()->(n=n+1);a=mk 0;b=mk 10;(a(),a(),b(),a(),b()))", .sequence [.zz 1,.zz 2,.zz 11,.zz 3,.zz 12]),
  ("(mk=n->()->(n=n+1);a=mk 0;b=a;(a(),b(),a()))", .sequence [.zz 1,.zz 2,.zz 3]),
  -- Local names avoid overwriting native M2's protected `set` library binding.
  ("(mk=n->(getter:=()->n;setter:=x->n=x;{getter,setter});fs=mk 7;(fs#1)12;(fs#0)())", .zz 12),
  ("(mk=x->y->()->(x=x+y);g=mk 10;a=g 2;b=g 3;(a(),b(),a()))", .sequence [.zz 12,.zz 15,.zz 17]),
  -- Global and local recursion; mutually recursive functions share declared cells.
  ("(fac=n->if n==0 then 1 else n*fac(n-1);fac 6)", .zz 720),
  ("(fac=n->if n==0 then 1 else n*fac(n-1);fac 0)", .zz 1),
  ("(f=()->(g:=n->if n==0 then 1 else n*g(n-1);g 5);f())", .zz 120),
  ("(f=()->(local g;g=n->if n==0 then 1 else n*g(n-1);g 5);f())", .zz 120),
  ("(fib=n->if n<2 then n else fib(n-1)+fib(n-2);fib 8)", .zz 21),
  ("(even=n->if n==0 then true else odd(n-1);odd=n->if n==0 then false else even(n-1);(even 8,odd 8))", .sequence [.bool true,.bool false]),
  ("(f=()->(local even;local odd;even=n->if n==0 then true else odd(n-1);odd=n->if n==0 then false else even(n-1);(even 6,odd 7));f())", .sequence [.bool true,.bool true]),
  ("(f=()->(local rec;rec=n->if n==0 then 0 else 1+rec(n-1);rec);g=f();g 10)", .zz 10),
  -- Return exits one invocation; all remaining operations are skipped.
  ("(f=x->(return x+1;1/0);f 6)", .zz 7),
  ("(f=x->(return;1/0);f 6)", .null),
  ("(f=x->(return 1,2;1/0);f 6)", .zz 1),
  ("(f=x->(return(1,2);1/0);f 6)", .sequence [.zz 1,.zz 2]),
  ("return 7", .zz 7),
  ("(f=()->(g=()->return 3;g()+4);f())", .zz 7),
  ("(f=x->(if x<0 then return -x;x);f(-4))", .zz 4),
  ("(f=x->(if x<0 then return -x;x);f 5)", .zz 5),
  ("(f=()->{1,return 7,1/0};f())", .zz 7),
  ("(f=()->1+(return 9);f())", .zz 9),
  ("(x=0;f=()->(x=3;return 7;x=99);r=f();(r,x))", .sequence [.zz 7,.zz 3]),
  ("(mk=n->()->(n=n+1;return n;n=999);f=mk 0;(f(),f()))", .sequence [.zz 1,.zz 2]),
  ("(f=()->(false and (return 3);7);f())", .zz 7),
  -- Multiple assignment preserves RHS class and evaluates it before any writes.
  ("(x=2;y=3;(x,y)=(y,x);(x,y))", .sequence [.zz 3,.zz 2]),
  ("((x,y):=(2,3);x+y)", .zz 5),
  ("((x,y)={2,3};x+y)", .zz 5),
  ("((x,y):={2,3})", .list [.zz 2,.zz 3]),
  ("(f=n->(n,n^2,n^3);(x,y,z)=f 3;{x,y,z})", .list [.zz 3,.zz 9,.zz 27]),
  ("(x=100;f=()->((x,y):=(2,3);x+y);(f(),x))", .sequence [.zz 5,.zz 100]),
  -- Predicate closures short circuit calls, including their side effects.
  ("(f=x->x>0;g=x->x<5;(f and g)3)", .bool true),
  ("(f=x->x>0;g=x->x<5;(f and g)7)", .bool false),
  ("(f=x->x>0;(not f)3)", .bool false),
  ("(f=x->false;g=x->1/0;(f and g)3)", .bool false),
  ("(f=x->true;g=x->1/0;(f or g)3)", .bool true),
  ("(counter=0;f=x->false;g=x->(counter=counter+1;true);(f and g)3;counter)", .zz 0),
  ("(counter=0;f=x->(counter=counter+1;true);g=x->(counter=counter+1;true);(f and g)3;counter)", .zz 2),
  -- Argument expressions, including collections, run left to right exactly once.
  ("(counter=0;f=(x,y)->(x,y,counter);f((counter=counter+1),(counter=counter+1)))", .sequence [.zz 1,.zz 2,.zz 2]),
  ("(counter=0;maker=()->(counter=counter+1;x->x);(maker()) (counter=counter+1);counter)", .zz 2),
  ("(f=x->{x,1/1,(2,3),{}};f(5/6))", .list [.qq (mkRat 5 6),.qq (mkRat 1 1),.sequence [.zz 2,.zz 3],.list []]),
  ("(f=x->\n x+1;f 4)", .zz 5),
  ("(f=(x,\ny)->(z:=x+y;\nz^2);f(2,3))", .zz 25),
  -- `local` reuses a current binding rather than redeclaring or resetting it.
  ("(x:=7;local x;x)", .zz 7),
  ("(local x;x=7;local x;x)", .zz 7),
  ("(f=()->(local x;x=7;local x;x);f())", .zz 7),
  ("(x:=local x;x==x)", .bool true),
  ("(f=()->(x:=local x;x==x);f())", .bool true),
  ("(f=x->x; f not false)", .bool true)
]

def errors : List (String × Error) := [
  ("(f=(x)->x;f())", .arity 1 0),
  ("(f=(x)->x;f(1,2))", .arity 1 2),
  ("(f=()->7;f 1)", .arity 0 1),
  ("(f=(x,y)->x+y;f {1,2})", .arity 2 1),
  ("(f=(x,y)->x+y;f(1,2,3))", .arity 2 3),
  ("(f=(x)->1/0;f())", .arity 1 0),
  ("(f=()->7;f(1/0))", .divByZero),
  ("(f=()->1/0;f())", .divByZero),
  ("(x=100;f=()->(x:=x+1;x);f())", .noMethod "+" ["Nothing","ZZ"]),
  ("(f=x->x+1;f -3)", .noMethod "-" ["FunctionClosure","ZZ"]),
  ("(f=x->x;f==f)", .noMethod "==" ["FunctionClosure","FunctionClosure"]),
  ("(f=x->x;g=f;f!=g)", .noMethod "!=" ["FunctionClosure","FunctionClosure"]),
  ("((x,y)=(2))", .assignmentArity 2 1),
  ("((x,y):=(1,2,3))", .assignmentArity 2 3),
  ("(f=()->true=7;f())", .protectedSymbol "true"),
  ("(f=x->x;f and true)", .noMethod "and" ["FunctionClosure","Boolean"]),
  ("(f=x->true;g=x->7;(f and g)3)", .noMethod "and" ["Boolean","ZZ"]),
  ("(f=x->7;(not f)3)", .noMethod "not" ["ZZ"]),
  ("(f=()->{1}#0=9;f())", .immutableCollection "List"),
  ("(f=()->return 1/0;f())", .divByZero),
  -- Right-associative application: parentheses are necessary around maker().
  ("(counter=0;maker=()->(counter=counter+1;x->x);maker() (counter=counter+1);counter)", .noMethod "SPACE" ["Sequence","ZZ"])
]

def invalidSyntax : List String := [
  "x ->", "-> x", "(x,x)->x", "((x,y))->x", "(1)->1", "1->1",
  "{x}->x", "(x,)->x", "(,x)->x", "local", "local 7", "local (x)",
  "x :=", "1 := 7", "(x,1) := (2,3)", "(x,1) = (2,3)", "return (1+)",
  "f(1,2", "(x)->(x+", "f = (x,y) -> (local; x)"
]
end Macaulean.M2.FunctionCases
