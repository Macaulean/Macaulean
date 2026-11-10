# M2 worksheets in Lean

```lean
import Macaulean.Interpreter.DSL
open M2

xs = {10, 20, 30};
saved = xs;
xs#-1
xs = xs | {40}
saved

{1/1, (2, 3), {}, ()}
(-2)..<2

if xs#?0 then xs#0 else 1/0
false and {}#0

example : 1 + 1 = 2 := by decide

#xs
```

The `.lean` file is a reproducible worksheet. Bare M2 inputs are separate Lean
commands, and their values and classes appear in the normal InfoView message
stream. No `#m2` prefix, quotation delimiter, source string, M2 executable, or
external server is needed by this interface.

## Architecture

`Parser.lean` is the single Pratt grammar for the string API and Lean DSL. It
constructs a concrete `Tree` retaining parentheses, keywords, delimiters, commas,
and token indices. `Tree.toTerm` erases presentation information. `Input.lean`
reads one REPL input and preserves UTF-8 byte locations. `DSL.lean` declares the
real `m2` syntax category and a scoped, low-priority bridge into Lean's `command`
category; `open M2` activates it. Structured syntax lowers directly to `Term`,
not through source printing and reparsing.

`Session.lean` contains only pure Lean values. A non-exported `EnvExtension`
attaches the immutable session to each Lean environment. Lean's incremental
command snapshots act as REPL checkpoints; importing another worksheet does
not import its variables, counter, output history, or active syntax scope.
There is no `IO.Ref`, external M2 process, or hidden execution engine in the DSL.

## Immutable lists and sequences

Lists and sequences are different value constructors, at every depth:

| Expression | Result |
| --- | --- |
| `{}` | Empty List |
| `()` | Empty Sequence, not null |
| `{7}` | One-element List |
| `(7)` | The integer 7; parentheses only group |
| `1:7` | One-element Sequence |
| `(1,)` | Two-element Sequence `(1, null)` |
| `{,}` | Two-element List `{null, null}` |
| `1,2,3` | Flat three-element Sequence |
| `((1,2),3)` | Nested Sequence; the first element is a Sequence |
| `{1..3}` | One-element List containing the Sequence `(1,2,3)` |

Commas associate left and bind below assignment and conditional branches. They
construct a sequence syntactically; parentheses prevent a comma chain from being
extended. A sequence-valued expression is never automatically spliced into a
containing list or sequence. Thus `x = 1, 2` binds `x` to 1 and returns `(1,2)`;
use `x = (1,2)` to bind the sequence. Omitted comma operands are actual `null`
values, not a trailing-comma convenience.

Elements evaluate left to right, sharing the surrounding variable environment.
Nested lists and sequences may contain integers, rationals, Booleans, null, and
other collections. Their printers retain integral-valued rationals as `1/1` and
use `1:(...)` for singleton sequences, so printing does not erase value classes.

### Ranges, repetition, concatenation

`m..n` is an inclusive increasing integer range; `m..<n` excludes the upper
endpoint. An empty or descending interval is an empty Sequence. Endpoints are
arbitrary-precision integers, not machine indices. Ranges materialize their
finite elements; huge requested cardinalities can exhaust ordinary elaborator
resources, and are not silently truncated.

`n:x` returns a Sequence repeating the value of `x` `max(n,0)` times. Both operands
are evaluated once, left to right, **even when n is zero or negative**. Thus
`0:(1/0)` errors; this is not a loop or a short-circuit construct.

`a | b` concatenates two Lists or two Sequences without changing their element
values or the operand collections. Mixed List/Sequence concatenation is rejected.

### Length and indexing

`#a` returns the number of elements. `a#i` returns an element, with zero-based
nonnegative indices and negative indices counting backward from the end.
An access index must be a ZZ value, not an integral-valued QQ. Invalid access
reports an error.

`a#?i` is an existence query: for a List or Sequence it returns false both for an
out-of-bounds integer and for a non-ZZ index, including Booleans, rationals, null,
and collections. `null#?i` also returns false. The query still evaluates both
operands, so an error in computing the index is not suppressed. Lists and
Sequences use the same positive and negative index bounds.

Prefix `#` binds below infix `#` and powers. For example, `#a#0` means `#(a#0)`.
All three infix operators `^`, `#`, and `#?` have the same precedence and associate
left. Ranges bind below addition; concatenation binds below ranges; repetition
binds below concatenation and associates right.

### Immutability and equality

An assignment may rebind a name to a new collection; it cannot alter an existing
collection value. An alias and a saved environment snapshot retain the old value
after rebinding. Indexed assignment syntax is recognized and rejected with an
immutable-collection error, rather than pretending to update an element.

M2 `==` and `!=` recursively compare collections of the same class. Numeric
promotion applies to their elements, so `{1} == {1/1}` is true. Different lengths
compare unequal before inspecting elements; comparison stops at the first
unequal element. Unsupported element comparisons propagate a method error.
List/Sequence equality does not coerce either outer constructor.

This semantic equality is separate from Lean's structural equality. The latter
retains every class tag and is used for checking exact interpreter results and
native differential observations.

## Branching and Boolean expressions

Supported constructs are `if condition then yes else no`, `if condition then
yes`, Boolean `and` and `or`, and prefix `not`. The condition must be a Boolean;
there is no numeric or collection truthiness. Only the selected branch is
evaluated. An omitted `else` returns `null` when the condition is false.

Boolean `false and rhs` and `true or rhs` skip `rhs` completely, including its
assignments and errors. Effects of evaluating the condition or left operand
are retained. The other Boolean cases evaluate the right operand and require
a Boolean result. Function-valued Boolean overloads are not implemented.

Precedence from higher to lower is comparisons, `not`, `and`, `or`, assignment.
`and` and `or` associate right. An `else` belongs to the nearest unmatched `if`.
Branches allow assignments, but unparenthesized semicolons and commas are outside
the conditional: use parentheses to include multiple expressions in a branch.

## Blocks, null, and input boundaries

A block `(x = 3; x + 4)` returns its last expression, here `7`. Blocks do not
introduce lexical scope. A trailing semicolon inside parentheses returns null:
`(x = 3;)` updates `x` without displaying an output. Empty `()` is instead an
empty Sequence and produces a visible output. Braces can also contain a block:
`{1;2}` is `{2}`, and `{1;}` is `{null}`, not an empty List.

A semicolon at top level ends the input and suppresses display. The original
string API keeps its `value` convention: `run "7;"` returns `7`, while
`run "(7;)"` returns `null`.

The protected binding `null` is available in the prelude. All successful
null-valued inputs suppress their output label and output-history entry, but
still advance the input counter and retain assignments. Empty collections do
not suppress output. Failures advance the input counter and report an error.

Newlines end inputs except inside parentheses or braces, after an operator with
a required operand or a branch keyword, and within an unfinished conditional
predicate. Inside a collection, a comma may span a newline. Inside a block,
newlines are whitespace, not statement separators: use `;` between assignments.

A completed top-level then-branch ends at a newline. Thus `if true then 1`
followed on the next line by `else 2` is not one valid input; put the conditional
in parentheses or put `else` on the same line as the completed then-branch.

## Error-state contract

The interpreter retains its **transactional per-input** contract. After
`x = 3;`, evaluating `(x = 99; 1/0)` or `{(x = 99), 1/0}` reports an error and
leaves the worksheet's `x` at `3`. Earlier successful inputs survive. This is an
explicit interpreter boundary, not a claim that native M2 rolls back side effects
on runtime errors. Changing the store/error model is a separate extension.

## Proofs and tests

`ControlFlow.lean` proves branch and block laws. `Collections.lean` proves
left-to-right element evaluation, error propagation, literal evaluation,
cardinalities, repetition's single evaluation, valid-index bounds, and rejection
of indexed mutation. The evaluator and nested equality decisions are structurally
recursive and kernel-executable; no new axioms, `sorry`, or `native_decide` are
introduced in this fragment.

The collection test files are:

- `CollectionCases.lean`: explicit typed expected data for success/error cases.
- `InterpreterCollections.lean`: kernel-checked result, error, malformed-input,
  precedence, large-integer, and typed-wire regressions.
- `InterpreterCollectionsDSL.lean`: a 63-input annotated bare-M2 worksheet,
  parser/formatter round trips, source positions, snapshots, and alias tests.
- `InterpreterCollectionsImport.lean`: cross-module state and syntax isolation.
- `InterpreterCollectionsM2.lean`: positive native comparisons, separate error
  controls, range/index grids, independent native parser-shape checks, and actual
  collection certificate generation.

The native oracle uses a typed preorder value format, not a source string to be
fed back into the parser under test. `Wire.lean` rejects unknown classes, truncated
structures, invalid counts, zero rational denominators, and extra data. Both
outer and nested scalar/collection classes are checked. Native M2 is required
only for the existing differential/certificate interface, not bare DSL execution.

All prior arithmetic and branching tests remain in the ordinary `MacauleanTest`
driver. The formerly unsupported `()` test now positively checks an empty Sequence.
Normal CI runs `lake build` and `lake test` with the pinned toolchain.

## Current scope and sources

The implemented grammar covers ZZ/QQ arithmetic, Boolean/null values, comparisons,
assignments, blocks, conditionals, short-circuit Boolean expressions, immutable
list/sequence construction, ranges, repetition, concatenation, length, and indexing.
It is not the full M2 library: collection arithmetic/ordering overloads, named
collection functions, strings, functions, loops, mutable collections, rings,
matrices, and symbolic unassigned globals remain outside this fragment.

Reference behavior was checked against M2's parser and operator registrations,
its documented collection conventions, and native M2 differential tests.

- [Lists](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/___List.html)
- [Sequences](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/___Sequence.html)
- [Operator precedence](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_precedence_spof_spoperators.html)
- [Concrete syntax trees](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_parse.html)
