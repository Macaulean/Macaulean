# M2 worksheets in Lean

```lean
import Macaulean.Interpreter.DSL
open M2

x = -7;
magnitude = if x < 0 then -x else x

half = 1/2;
half + 1/3

false and (1/0 == 0)
if true then (x = 3; x + 4) else 1/0

example : 1 + 1 = 2 := by decide

x + 10
```

The `.lean` file is a reproducible worksheet. Bare M2 inputs are separate Lean
commands, and their values and classes appear in the normal InfoView message
stream. No `#m2` prefix, quotation delimiter, source string, M2 executable, or
external server is needed by this interface.

## Architecture

`Parser.lean` is the single Pratt grammar for the string API and Lean DSL. It
constructs a concrete `Tree` retaining parentheses, keywords, delimiters, and
token indices. `Tree.toTerm` erases presentation information. `Input.lean` reads
one REPL input and preserves UTF-8 byte locations. `DSL.lean` declares the real
`m2` syntax category and a scoped, low-priority bridge into Lean's `command`
category; `open M2` activates it. Structured syntax lowers directly to `Term`,
not through source printing and reparsing.

`Session.lean` contains only pure Lean values. A non-exported `EnvExtension`
attaches the immutable session to each Lean environment. Lean's incremental
command snapshots act as REPL checkpoints; importing another worksheet does
not import its variables, counter, output history, or active syntax scope.
There is no `IO.Ref`, external M2 process, or hidden execution engine in the DSL.

## Branching and Boolean expressions

Supported constructs are `if condition then yes else no`, `if condition then
yes`, Boolean `and` and `or`, and prefix `not`. The condition must be a Boolean;
there is no numeric truthiness. Only the selected branch is evaluated. An omitted
`else` returns `null` when the condition is false.

Boolean `false and rhs` and `true or rhs` skip `rhs` completely, including its
assignments and errors. Effects of evaluating the condition or left operand
are retained. The other Boolean cases evaluate the right operand and require
a Boolean result. Function-valued Boolean overloads are not implemented.

Precedence from higher to lower is comparisons, `not`, `and`, `or`, assignment.
`and` and `or` associate right. An `else` belongs to the nearest unmatched `if`.
Branches allow assignments, but an unparenthesized semicolon is outside the
conditional: use a block when multiple expressions belong to a branch.

## Blocks, null, and input boundaries

A block `(x = 3; x + 4)` returns its last expression, here `7`. Blocks do not
introduce lexical scope. A trailing semicolon **inside** parentheses returns
`null` after performing the preceding computations: `(x = 3;)` updates `x`
without displaying an output. Empty `()` is an M2 Sequence, not a scalar block,
and is outside this fragment; it is rejected rather than reinterpreted as null.

A semicolon **at top level** ends the input and suppresses display. The original
string API keeps its `value` convention: `run "7;"` returns `7`, while
`run "(7;)"` returns `null`.

The protected binding `null` is available in the prelude. All successful
null-valued inputs suppress their output label and output-history entry, but
still advance the input counter and retain assignments. Failures also advance
the input counter and report an error instead of a value.

Newlines end inputs except inside parentheses, after an operator or branch
keyword, and within an unfinished conditional predicate. For example:

```lean
open M2

if
  1 < 2
then
  7

(if true then
  1
else
  2)

if false then 1 else
  2
```

A completed top-level then-branch ends at a newline. Thus `if true then 1`
followed on the next line by `else 2` is not one valid input; put the conditional
in parentheses or put `else` on the same line as the completed then-branch.
Inside a block, newlines are whitespace, not statement separators: use `;`
between assignments.

## Error-state contract

This extension retains the parent interpreter's **transactional per-input**
contract. For example, after `x = 3;`, evaluating `(x = 99; 1/0)` reports an
error and leaves the worksheet's `x` at `3`. Earlier successful inputs survive.
This is a stated interpreter boundary, not a claim that native M2 rolls back
all side effects on every runtime error. Changing the store/error model is a
separate extension. Short-circuiting and branch selection introduce no effects
from expressions that are not evaluated.

## Proofs and tests

`Macaulean/Interpreter/ControlFlow.lean` proves general laws for branch selection,
short-circuit non-execution, environment threading, block sequencing, and session
state preservation. The evaluator remains structurally recursive and directly
kernel-executable; there are no added axioms or `sorry` proofs.

The original 60-input `InterpreterDSL.lean` worksheet, import-isolation suite,
printer regressions, arithmetic kernel examples, and live-M2 checks remain.
Additional test modules are:

- `InterpreterBranching.lean`: kernel-checked outcomes, errors, syntax rejection,
  precedence, concrete AST association, nested conditionals, and block semantics.
- `InterpreterBranchingDSL.lean`: a 59-input annotated worksheet plus structured
  syntax, UTF-8 source ranges, input boundaries, snapshots, and formatter tests.
- `InterpreterBranchingImport.lean`: cross-module state and scope isolation.
- `InterpreterBranchingM2.lean`: native-M2 value/class comparisons that require
  success on both sides, separate error controls, and independent checks of
  native `parse` tree shapes. External M2 is used only in these tests.

Everything is imported by the ordinary `MacauleanTest` driver; normal CI runs
`lake build` and `lake test` with the repository's pinned toolchain.

## Current scope and sources

The supported language is ZZ/QQ arithmetic, Boolean and null values, comparisons,
assignments, sequencing, conditionals, short-circuit Boolean expressions, and
parenthesized blocks. Rings, matrices, functions, lists/sequences, loops,
function-valued operator overloads, and symbolic unassigned globals remain
outside this fragment.

Reference behavior was checked against M2's `unaryif` and `unaryparen` in
`M2/Macaulay2/d/parser.d`, precedence registration in `binding.d`, and Boolean
dispatch in `actors.d`, as well as native M2 differential tests.

- [Conditionals](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_if.html)
- [Operator precedence](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_precedence_spof_spoperators.html)
- [Concrete syntax trees](https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Macaulay2Doc/html/_parse.html)
