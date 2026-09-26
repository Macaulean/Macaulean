# M2 worksheets in Lean

```lean
import Macaulean.Interpreter.DSL
open M2

makeCounter = start -> (n := start; () -> (n = n+1));
next = makeCounter 0;
next()
next()

xs = {10,20,30};
xs#-1

factorial = n -> if n == 0 then 1 else n*factorial(n-1);
factorial 6

example : 1 + 1 = 2 := by decide
```

The `.lean` file is a reproducible worksheet. Bare M2 inputs elaborate as separate
Lean commands, with values and classes in the normal InfoView message stream.
No `#m2` prefix, quotation delimiter, source string, M2 executable, or external
server is needed by this interface. `open M2` activates its scoped syntax.

## Architecture and execution

`Parser.lean` is the single Pratt grammar shared by the string API and Lean DSL.
It constructs a concrete tree retaining parentheses, keywords, delimiters,
commas, and token indices. `Input.lean` reads one REPL input and preserves UTF-8
byte locations. `DSL.lean` declares the real `m2` syntax category and a scoped,
low-priority bridge into Lean's `command` category. Structured syntax lowers
directly to `Term`, not through printing and reparsing.

`Lexical.lean` resolves local bindings in source order. `Runtime.lean` evaluates
resolved code with an explicit depth budget and a pure heap of lexical cells and
closures. Both `run` and bare worksheet commands use this runtime. Arithmetic
and collection primitives are shared with the original loop-free reference
`evalTerm`, which is retained for existing semantic theorems.

`Session.lean` contains only pure Lean values. A non-exported `EnvExtension`
attaches the whole session, including closure records and captured cells, to each
Lean environment. Incremental command snapshots act as REPL checkpoints.
Importing a worksheet does not import its variables, closures, counter, output
history, file-local bindings, or active syntax scope. There is no `IO.Ref` or
external execution engine in the DSL.

## Functions and lexical binding

```lean
open M2
square = x -> x^2;
add = (x,y) -> x+y;
answer = () -> 42;
square 7
add(2,3)
answer()
```

Functions are first-class values: arguments, return values, and collection
members can all be functions. `x -> body` accepts an arbitrary operand, including
a Sequence of arguments. `(x) -> body` requires exactly one argument; `(x,y)`
requires two and `()` requires none. A fixed-arity function unpacks a Sequence,
not a List. Parameter parentheses are significant syntax, not ordinary grouping.

Application is adjacency and associates right: `f g x` means `f(g x)`. Powers and
indexing bind more tightly, so `f(3)^2` means `f(3^2)`. Use `(f 3)^2` for the
other grouping. Negative arguments need parentheses: `f -3` is subtraction.
Composition `f @@ g` and function-valued Boolean `and`, `or`, and `not` work.
Predicate combinations short circuit the calls they perform.

`x := value` declares a new local in the innermost function body or current file,
before resolving the initializer. `x = value` updates the lexically selected
binding, or the global if none is visible. Blocks and collection literals do not
introduce scopes. Source-ordered resolution preserves an earlier reference when
a later local declaration uses the same spelling. Redeclaration with `:=`
allocates a fresh cell and warns. `local x` instead reuses the current-scope x if
present, introduces it otherwise, and returns its Symbol without assigning it.

Closures capture cell addresses, not value copies. Escaping siblings share their
captured updates; distinct factory calls have independent cells. Global and
local recursion, mutual recursion, and early return are supported. `return x`
exits the current invocation; `return` uses null. Multiple assignment and local
binding `(x,y) = result` / `(x,y) := result` accept a matching List or Sequence,
evaluate the right side once, and preserve its class as the expression result.

See [Functions and lexical binding](m2-functions.md) for examples, the static
resolver/store design, error and resource contracts, and the test suites.

## Immutable lists and sequences

| Expression | Result |
| --- | --- |
| `{}` | Empty List |
| `()` | Empty Sequence, not null |
| `{7}` | One-element List |
| `(7)` | Integer 7; grouping only |
| `1:7` | One-element Sequence |
| `(1,)` | Two-element Sequence `(1, null)` |
| `{,}` | Two-element List `{null, null}` |
| `1,2,3` | Flat three-element Sequence |
| `((1,2),3)` | Nested Sequence |
| `{1..3}` | One-element List containing a Sequence |

Commas associate left and bind below assignment and conditional/function bodies.
Parentheses prevent a comma chain from being extended. Sequence-valued
expressions are never automatically spliced. `x = 1,2` binds x to 1 and returns
`(1,2)`; `x = (1,2)` binds the Sequence. Omitted comma operands are actual nulls.

Elements evaluate left to right. Lists and sequences may nest and contain any
implemented value, including closures. Printers retain scalar/collection classes:
integral-valued rationals print as `1/1` and singleton sequences as `1:(...)`.
Function handles have opaque display labels, not serializable captured source.

### Ranges, repetition, concatenation, and indexing

`m..n` is an inclusive increasing integer range; `m..<n` excludes n. Descending
or empty intervals return an empty Sequence. `n:x` repeats the value of x
`max(n,0)` times. It evaluates both operands once, even when n is zero or negative;
`0:(1/0)` errors. `a | b` concatenates two Lists or two Sequences, without changing
either operand; mixed outer classes are rejected.

`#a` gives length. `a#i` uses zero-based indices, with negative indices counting
from the end. Invalid access errors. `a#?i` reports validity, returning false for
out-of-range or non-ZZ indices; it does not coerce an integral-valued QQ index.
`null#?i` also returns false. Prefix `#` binds below infix `#` and powers, so
`#a#0` means `#(a#0)`.

Assignment can rebind a collection name but cannot mutate its contents. Indexed
assignment is recognized and raises an immutable-collection error. `==` and `!=`
recursively compare same-class collections with numeric promotion of elements.
Different lengths compare unequal; element comparison stops at the first
inequality. Unsupported element comparisons, including function equality,
propagate a method error. This is distinct from Lean's structural equality,
which preserves every constructor tag and is used by exact-result tests.

## Branches, blocks, and input boundaries

`if condition then yes else no` requires a Boolean condition and evaluates only
the selected branch. Omitted else produces null for a false condition. Boolean
`false and rhs` and `true or rhs` skip all of rhs, including assignments and errors.
Comparisons bind more tightly than `not`, then `and`, then `or`; and/or associate
right. An else belongs to the nearest unmatched if.

A block `(x=3; x+4)` returns its last expression and creates no scope. An internal
trailing semicolon returns null after the prior work: `(x=3;)`. Braces can contain
a block: `{1;2}` is `{2}` and `{1;}` is `{null}`. Empty `()` is a visible empty
Sequence, not a null-valued block.

A top-level semicolon ends an input and suppresses output. The legacy string API
keeps its value convention: `run "7;"` returns 7 while `run "(7;)"` returns null.
All successful null outputs are silent but retain assignments and consume an
input number. Empty collections are not silent. Failures also advance the input
number and show an error rather than a value.

Newlines end inputs except inside parentheses/braces, after an operator with a
required operand, after branch/arrow/local keywords, or within an unfinished if
predicate. Inside parentheses/braces, newlines are whitespace rather than
implicit semicolons; adjacent expressions can therefore be function application.
A completed top-level then-branch ends at a newline: put else on the same line,
or surround the conditional with parentheses. A bare return ends at a newline.

## Error and resource contracts

Errors are **transactional per input**, including captured-cell writes. After
`x=3;`, either `(x=99;1/0)` or `{(x=99),1/0}` leaves x at 3. Likewise, a failed
input that calls a counter does not commit its captured update. This is the
interpreter's stated contract, not a claim that native M2 rolls back all effects.
Early return is successful control flow and preserves prior writes.

Recursion is bounded by an explicit evaluation-depth budget, default 4096.
`set_option m2.maxDepth 8192` changes it for worksheet elaboration; `runWithFuel`
and `Session.step` expose it directly. Exhaustion errors and rolls back the input;
it does not fabricate null or a successful partial result. This is not a bound
on total work or memory. Large finite ranges, branching recursion, and the current
append-only heap can consume substantial resources.

## Proofs, tests, and certificates

The normal test driver retains the original arithmetic, branching, and collection
worksheets, their semantic laws, printer/source-range tests, import isolation,
and native differential suites. The function extension adds an 80-input annotated
worksheet, explicit kernel/native reference corpora, fixed/variable-arity parser
checks, captured-state snapshots, recursion failure and recovery, and its own
import-isolation module.

`Functions.lean` proves generic facts about the actual lexical runtime and its
resolver: capture and call frames, arity, fresh allocation, branch/return behavior,
and rollback. It also proves the actual runtime preserves the original integer
semantics for arbitrary integer expressions when sufficient depth is provided.
The older `Semantics`, `ControlFlow`, and `Collections` laws for loop-free
`evalTerm` remain clearly scoped reference results.

The independent native oracle supplies typed preorder data, not source text for
the parser under test. `Wire.lean` rejects malformed data, zero denominators,
truncated structures, trailing data, and unsupported classes. It does not import
foreign function handles or lexical cells. Native M2 is used by the differential
and certificate interface only, not bare DSL execution. Function programs whose
results are scalar/collection data can create kernel-checked `run` equalities
through `#m2_check`; the external answer is never accepted as an axiom.

## Current scope

The grammar includes scalar arithmetic, Boolean/null values, immutable
collections, assignment, blocks, branching, functions, lexical binding, recursion,
return, and the operators described above. It is not the entire M2 language or
standard library. Named library functions, method/optional-argument dispatch,
strings, loops, mutable collections, rings, matrices, and general symbolic
unassigned globals remain separate fragments. Unassigned globals retain the
previous interpreter's explicit unbound-name error.

Reference sources and detailed function semantics are in
[the function-extension documentation](m2-functions.md).
