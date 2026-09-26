# Functions, closures, and lexical binding

The function fragment is part of the ordinary `open M2` language. It needs no
per-input prefix, quotation, native M2 executable, or separate runtime process.

```lean
import Macaulean.Interpreter.DSL
open M2

makeCounter = start -> (n := start; () -> (n = n+1));
a = makeCounter 0;
b = makeCounter 100;

a()
-- 1 : ZZ

a()
-- 2 : ZZ

b()
-- 101 : ZZ

alias = a;
alias()
-- 3 : ZZ

a()
-- 4 : ZZ
```

See `MacauleanTest/InterpreterFunctionsDSL.lean` for the executable, annotated
worksheet. Its `#guard_msgs` wrappers are test assertions, not syntax required
by ordinary users.

## Calling conventions

| Function syntax | Parameter convention |
| --- | --- |
| `x -> body` | Bind the entire operand to x, including an empty or multi-element Sequence |
| `(x) -> body` | Require exactly one argument; unwrap a singleton Sequence |
| `(x,y) -> body` | Require exactly two arguments in a Sequence |
| `() -> body` | Require an empty Sequence |

Lists are values, not argument packs. A fixed two-argument function rejects
`f {1,2}` but accepts `f(1,2)`. `(x) -> x` accepts the List `{1,2}` as its one
argument. By contrast, `x -> x` applied to `(1:7)` returns the singleton Sequence,
while `(x) -> x` returns the integer 7. The concrete parser therefore retains
parameter parentheses until it has determined the calling convention.

Argument expressions are evaluated before arity checking, from left to right.
The function expression is evaluated before its argument expression. Function
bodies execute only when called; defining a function containing `1/0` is valid.

Functions are first-class: they may be passed as arguments, returned, assigned,
or stored in arbitrarily nested immutable collections. Partial application is
expressed by explicitly returning a function, for example `x -> y -> x+y`;
a fixed-arity function does not automatically curry missing arguments.

## Application and operators

Application is adjacency. Its binding power lies below powers/indexing and
composition but above multiplication. It associates right:

| Source | Meaning |
| --- | --- |
| `f g x` | `f(g x)` |
| `f(3)^2` | `f(3^2)` |
| `(f 3)^2` | Square the result of calling f |
| `f 3 * 2` | `(f 3) * 2` |
| `f -3` | Subtraction, not application to a negative argument |
| `f(-3)` | Application to the negative integer |
| `(maker()) x` | Call a returned function; parentheses around `maker()` matter |

`f @@ g` composes functions, calling g first. Function-valued `and`, `or`, and
`not` construct predicate functions. The combined predicate passes its operand
to the component functions and short circuits their calls in the Boolean cases.
Skipped calls neither raise errors nor modify captured cells.

The established scalar and collection operators remain available inside bodies.
Functions do not acquire structural M2 `==` merely because their Lean handles
have decidable equality: M2 function equality through `==`/`!=` reports a method
error. Native differential checks compare observable call results, not handles
or an invented extensional equality.

## Lexical declarations

`x := expression` declares a fresh local binding in the innermost function, or
in the current worksheet's file scope. The binding exists before its initializer
is resolved. Uninitialized local cells contain `null`, so `x := x` initializes
the new cell with null, not with an outer x.

`x = expression` updates the statically selected binding. Without a visible local
binding, it updates the global name. Parameters are local cells. Parentheses,
blocks, conditionals, and collection literals do not introduce lexical scopes.

Binding is source-ordered, not dynamically chosen by the caller. For example:

```m2
x = 100;
f = () -> x;
x := 7;
g = () -> x;
x = 8;
(f(),g(),x)
-- (100,8,8)
```

The earlier f still refers to global x. The later g refers to the file-local
cell and observes its updates. Repeating `x := ...` creates another cell and
emits a redeclaration warning; previously created closures keep their earlier
bindings. `local x` is different: it reuses the current scope's x when one exists,
introduces it otherwise, and returns the corresponding Symbol without assigning
that Symbol to the cell.

Resolution visits unselected branches too. In
`f = () -> (if false then x := 7; x)`, x is a local in the final expression,
even though its initializer is never run; the call returns null.

A worksheet's file scope persists across its M2 commands. Opening the M2 syntax
namespace is not itself a new M2 lexical scope. Importing another Lean module
does not import that module's interactive session or lexical cells.

## Captures, recursion, and return

Escaping closures refer to shared cells, not copies of captured values:

```m2
makePair = () -> (n := 0; (() -> (n=n+1), () -> n));
pair = makePair();
(pair#0)();
(pair#1)()
-- 1
```

Each invocation of `makePair` allocates different cells. Copying a function value
or storing it in a collection preserves its identity within the session, so
aliases share captured updates. Rebinding an alias name does not change another
alias or mutate an earlier Lean elaboration snapshot.

Both global and local recursive definitions work. A local recursive initializer
can refer to its own newly declared cell. Mutual local recursion can be written
with `local f; local g;` before assigning either body, ensuring that each body
resolves the other name to the intended local cell.

`return expression` exits the current function invocation and retains prior
writes. It propagates through argument evaluation, collections, branches, and
blocks until the invocation boundary. An inner function's return does not exit
its caller. Bare `return` uses null. At the top level it finishes the current
source evaluation / worksheet input. Commas bind below return: `return 1,2`
returns 1, whereas `return(1,2)` returns a Sequence.

Multiple assignment `(x,y) = result` and multiple local declaration
`(x,y) := result` accept a List or Sequence with matching length. The RHS is
evaluated once, before any writes, and the assignment expression preserves its
class. Local targets are all introduced before resolving the RHS; use `=` rather
than `:=` to swap existing local values.

## Pure implementation

The implementation separates syntax, lexical resolution, and execution:

1. The shared Pratt parser constructs the semantic `Term` and located concrete
   syntax. The Lean adapter lowers structured `Syntax` directly to that AST.
2. `Lexical.prepare` resolves each name to either a global or a `(depth, slot)`
   reference. A lambda stores its parameter convention, local-slot count, and
   resolved body. Name lookup in a dynamic caller never determines capture.
3. `Runtime` represents the heap using ordinary immutable Lean lists. Cells hold
   values; a separate function table holds resolved code and captured frame
   addresses. Values contain session-relative handles, allowing self-reference
   and mutually recursive closures without cyclic Lean values.
4. Calling a closure checks arity, allocates a fresh frame, and installs its saved
   lexical frames beneath that frame. Writes return a new heap. They do not use
   `IO.Ref`, mutable external storage, a foreign interpreter, or native evaluation
   as a proof oracle.
5. `Session.step` carries the heap, global environment, file scope, and file frame
   between commands. The entire session belongs to Lean's non-exported environment
   extension, so incremental snapshots include captured state as well as names.

`run` and the DSL both execute this resolved runtime. The original `evalTerm`
remains the loop-free reference evaluator for existing arithmetic/collection
proofs; it explicitly rejects constructs requiring the lexical runtime rather
than pretending to evaluate them. Clients evaluating source should use `run`,
`runWithFuel`, `Runtime.evaluate`, or `Session.step` as appropriate.

A bare Value handle is not a portable closure. `Runtime.evaluate` returns the
state needed to use it, and `Session` retains that state. Printed function labels
are inspection aids, not source expressions that reconstruct captured variables.
The native wire decoder rejects foreign function handles and symbolic cells,
including handles nested inside otherwise supported collections.

## Error and resource contracts

The existing transaction boundary is one input. Any runtime error or exhausted
evaluation budget discards that input's global writes, cell writes, new closures,
and new file-local bindings. Earlier successful inputs and their output history
survive. A failed input advances the input counter but has no successful output.
This deliberate interpreter contract is not a claim that native M2 rolls back
all effects on errors. Early return is successful control flow, not rollback.

Mutually recursive evaluation and calls decrease an explicit depth budget.
The default is 4096. Use `set_option m2.maxDepth 8192` in a worksheet, or an explicit
budget with `runWithFuel` / `Session.step`. Exhaustion is an error, not null or
successful truncation. The budget bounds evaluation depth, not total work,
collection cardinality, or memory. The current heap is append-only; it has no
garbage collector. These resource choices do not add an axiom or an unchecked
termination assumption to the interpreter.

## Tests and proof boundary

`Functions.lean` proves laws about the actual resolved runtime: calling
conventions, fresh declarations, capture and call frames, allocation, early
return, branch selection, short circuiting, and whole-session rollback. Its
`IntExpr.runtime_eval` and `runtime_evaluate` theorems establish the original
integer denotation in the new runtime for arbitrary expressions with sufficient
budget. The retained loop-free proofs remain explicitly about `evalTerm`.

The test driver includes the 80-input worksheet; a shared explicit kernel/native
result and error corpus; additional lexical edge cases; independent native
parser-shape and malformed-binder controls; UTF-8 positions and formatting;
function-valued collection members; live captured-state aliases; old snapshots;
recursion exhaustion and recovery; and cross-module isolation. Native comparisons
require successful typed observations on both sides. Native syntax controls
explicitly discard valid function results before serialization, so rejection of
an unsupported wire class cannot masquerade as a syntax error.

The certificate interface proves equalities about `run` using the Lean kernel.
A native M2 answer is only a comparison target, never an axiom. This does not
constitute a general formal proof that the interpreter implements all native M2
semantics, and it does not certify extensional equality of functions.

## Scope and references

This fragment includes arrow functions, application, fixed and variable arity,
lexical `:=` and `local`, multiple assignment, captured updates, recursion,
return, composition, and predicate combinations. Named standard-library functions,
method/optional-argument dispatch, general symbolic unassigned globals, loops,
strings, mutable collection objects, rings, and matrices remain separate fragments.
Only the implemented prelude's global names are protected by this interpreter;
it does not pretend to preload the native M2 standard library.

Reference behavior is tested against native Macaulay2 in the repository's CI.
The relevant primary references are:

- [Function construction and argument conventions](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_-_gt.html)
- [Local declaration](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/__co_eq.html)
- [Operator precedence](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_precedence_spof_spoperators.html)
- [Native parser](https://github.com/Macaulay2/M2/blob/stable/M2/Macaulay2/d/parser.d)
- [Native binding and operator registration](https://github.com/Macaulay2/M2/blob/stable/M2/Macaulay2/d/binding.d)
