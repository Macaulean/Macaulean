# M2 worksheets in Lean

```lean
import Macaulean.Interpreter.DSL
open M2

x = 7;
x^2

half = 1/2;
half + 1/3

example : 1 + 1 = 2 := by decide

x + 10
```

The nonsuppressed inputs report `o2 = 49 : ZZ`, `o4 = 5/6 : QQ`,
and `o5 = 17 : ZZ` through Lean's ordinary message/InfoView machinery.
No `#m2` prefix, quotation delimiter, string literal, M2 executable, or
external server is involved.

## Architecture

* `Parser.lean` is the single Pratt grammar. It now constructs a concrete
  `Tree` retaining parentheses and token indices. `Tree.toTerm` erases only
  presentation information and yields the existing semantic `Term`.
* `Input.lean` reads exactly one REPL input and retains UTF-8 byte locations.
  Semicolon and newline termination follow M2 rules.
* `DSL.lean` declares the real `m2` syntax category and installs a scoped,
  low-priority bridge into Lean's `command` category. Plain `open M2`
  activates it.
* The command elaborator lowers structured `Lean.Syntax` directly to `Term`;
  it does not print and reparse source.
* `Session.lean` is pure Lean state. The current session is an immutable value
  in a non-exported `EnvExtension`; there is no `IO.Ref`, native M2 process,
  or hidden runtime evaluator.

Every M2 input is a separate Lean command, so Lean's normal incremental
elaboration snapshots act as REPL checkpoints. Editing an earlier input causes
the downstream worksheet to be elaborated again from the corresponding prior
environment.

## Input boundaries

A semicolon terminates one input and suppresses its display. A newline terminates
an input except after an operator or inside parentheses. Thus both of these are
single inputs:

```lean
open M2
1 +
2

(1
 + 2)
```

while this is two inputs:

```lean
1
+2
```

The existing ZZ/QQ evaluator remains transactional within one input. Failed
inputs advance the input number but do not replace the previous environment.

## Tests

`MacauleanTest/InterpreterDSL.lean` is an executable 60-input worksheet plus
metaprogramming regressions. It covers:

* persistent assignment and rebinding;
* ordinary Lean declarations interleaved with M2;
* semicolon suppression and multiple inputs on one physical line;
* ZZ/QQ class preservation;
* Euclidean quotient/remainder sign combinations and zero divisors;
* M2 unary-minus and power precedence;
* multiline continuation and newline termination;
* comments and UTF-8 source ranges;
* base-prefixed literals and M2-style identifiers;
* errors followed by recovery;
* structured syntax and agreement with the string parser;
* environment snapshot branching;
* scope deactivation.

`MacauleanTest/InterpreterDSLImport.lean` checks that importing a worksheet
does not import its M2 variables, transcript, counter, or active syntax scope.

The full repository CI builds these through the normal `MacauleanTest` driver.

## Current scope

This frontend intentionally exposes the same interpreter fragment as the stacked
interpreter PR: ZZ/QQ arithmetic, comparisons, assignments, and statements.
It does not yet implement the full Macaulay2 language (rings, matrices,
functions, lists, control flow, symbolic unassigned globals, etc.).
