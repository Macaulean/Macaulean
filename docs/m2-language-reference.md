# Supported M2 dialect

This is the scope and semantics entry point for the implemented Macaulean DSL.
It describes the production parser/resolver/runtime on the #49 stack; it is not
an exhaustive Macaulay2 specification or a claim of native-M2 equivalence.
The user-facing worksheet guide is [M2 worksheets](m2-dsl.md). Detailed algebra
and proof interfaces are linked below rather than assigned a single blanket
“supported” label. Expert review of the dialect choices remains open (roadmap A7).

## Execution interfaces

| Interface | Meaning and state boundary |
| --- | --- |
| `import Macaulean.Interpreter.DSL; open M2` | Bare M2 inputs become worksheet commands. Each input commits on success and rolls back on error. Lean declarations may be interleaved. |
| `run source` / `runWithFuel fuel source` | Parse a source string and execute it from the default runtime state, returning `Outcome.ok`, `Outcome.error`, or `Outcome.parseError`. This is not a persistent REPL. |
| `Session.step` | Execute one parsed input in an explicit pure session, retaining bindings, cells, rings, and output numbering across successful inputs. |
| Exported worksheet definitions | Persistent Lean declarations capture a particular worksheet revision. They do not automatically become total typed algorithms; see [definition exposure](m2-definition-exposure.md). |

`Parser.lean` supplies the shared concrete-tree grammar; `Lexical.lean` resolves
names; `Runtime.lean` executes resolved code. The legacy `evalTerm` is a
restricted reference evaluator, not the general function/closure execution API.
Session/worksheet calls to the public polynomial `gcd` value have a special
proved input-derived budget handler; raw `runWithFuel` retains its explicit
budget. See [GCD](m2-gcd.md) for the supported univariate QQ domain and theorem
hypotheses. A depth allowance is not a bound on total work, heap size, or memory.

## Supported-feature matrix

“Restricted” means the implemented boundary is intentional and documented. It
does not mean every native overload is available. A rejected form can be valid
native M2; it must not be labeled a native syntax error solely from DSL rejection.

| Area | Execution support | Boundary and evidence |
| --- | --- | --- |
| Integers and rationals | Exact ZZ/QQ arithmetic, decimal and binary/octal/hex integer literals | Rational values arise from operations such as division; floating literals and approximate arithmetic are outside the dialect. [Arithmetic tests](../MacauleanTest/Interpreter.lean) |
| Boolean and null | `true`, `false`, `null`, strict Boolean branching, short-circuit `and`/`or` | Numbers are not truth values. [Branching](../MacauleanTest/InterpreterBranching.lean) |
| Collections | Immutable Lists and Sequences, nesting, omitted operands, ranges, repetition, concatenation, indexing | No automatic splicing or mutable elements. List and Sequence remain distinct classes. [Worksheet](m2-dsl.md#immutable-lists-and-sequences) |
| Bindings and functions | `=`, `:=`, `local name`, closures, fixed/variadic arguments, recursion, composition, early return | Cells are shared by closures; a block creates no scope. No method table, keyword/options argument dispatch, or keyword quotation. [Functions](m2-functions.md), [quotation boundary](m2-keyword-boundary.md) |
| Symbols | Identifier Symbols from `local name`, lexical bracket bindings for rings | General unassigned-global symbolic evaluation and first-class Keyword/operator quotation are not implemented. |
| Polynomial rings | Fresh `QQ[...]` rings, scalar promotion, sparse polynomials, fixed grevlex | Other coefficient rings/orders, general indexed-name syntax and fraction fields are outside this interface. [Polynomials](m2-polynomials.md) |
| Ideals and matrices | Ideals, generator rows, basis/change-matrix containers, inspected dimensions and the matrix products used by provenance | Restricted algebra containers, not arbitrary module APIs or mutable matrices. [Matrix dimensions](m2-groebner.md#provenance-and-matrix-dimensions) |
| Named library functions | Tracked `Buchberger.m2` and `GCD.m2`; public `gb`, `normalForm`, `sPolynomial`, `gcd` | These are source-library functions and aliases, not package loading or general native dispatch. [Library source map](../Macaulean/Interpreter/Library.lean) |
| Reduction and Gröbner bases | Ordered reduction and all-pairs Buchberger execute in Lean | A `GroebnerBasis` runtime value or a successful example is not a universal correctness theorem. [Execution and proof boundary](m2-groebner.md) |
| Packages and external methods | No general package-loading language or extensible native method system | The original external certificate/RPC route is separate from pure DSL execution. |
| Strings, floats, subscripts | Not implemented by the lexer/parser | Do not confuse a ring's internal generated names with accepted `x_0` source syntax. |
| Loops and mutable collections | No `for`/`while` constructs or element mutation | Recursion is available. Loop words are ordinary identifiers, not reserved loop syntax. Indexed assignment is parsed but rejected at runtime. |

## Lexical and input rules

Identifiers begin with an alphabetic character; later characters can be
alphanumeric, apostrophe, or `$`. `_` is not an identifier character. `--` starts
a line comment. The reserved words are `if`, `then`, `else`, `and`, `or`, `not`,
`local`, and `return`. Boolean/null names and prelude functions are bindings;
not every native-M2 keyword is reserved here. See
[`Lexer.lean`](../Macaulean/Interpreter/Lexer.lean) for the exact token set.

Newlines end worksheet inputs unless delimiters, an operator, or an unfinished
keyword form requires more input. Inside parentheses/braces they are whitespace,
not implicit semicolons. Put an `else` on the same input as its `then` branch, or
parenthesize the conditional. A top-level semicolon suppresses output; an internal
trailing semicolon makes a block return null. `(7)` is grouping, `()` an empty
Sequence, `{7}` a List, and `1:7` a singleton Sequence. `(1,)` includes a null.
See [input boundaries](m2-dsl.md#branches-blocks-and-input-boundaries).

## Precedence and associativity

Higher rows bind more tightly. These are the implemented Pratt binding powers,
not inferred from Lean syntax or an algebraic convention. Parentheses can always
make a desired grouping explicit. `Parser.infixInfo` is authoritative.

| Binding power | Forms | Association |
| --- | --- | --- |
| 55 | Polynomial-ring bracket constructor | Postfix |
| 50 | `^`, `#`, `#?` | Left |
| 48 | `@@` | Left |
| 46 | Adjacency application | Right |
| 45 | Prefix `#` | Prefix operand threshold |
| 40 | `*`, `/`, `//`, `%` | Left |
| 35 | Unary `+`, `-` | Prefix operand threshold |
| 30 | `+`, `-` | Left |
| 25 | `..`, `..<` | Left |
| 23 | `|` | Left |
| 22 | `:` | Right |
| 20 | `==`, `!=`, `===`, `=!=`, `<`, `<=`, `>`, `>=` | Right; not chained-comparison logic |
| 19 | `not` | Prefix operand threshold |
| 18 / 16 | `and` / `or` | Right |
| 10 | `=`, `:=`, `->`; conditional/return bodies | Right for infix forms |
| 5 | `,` | Left, with grouping retaining nested Sequences |

In particular, `2^3^2` is `(2^3)^2`; `f g x` is `f(g x)`; `f(3)^2` is
`f(3^2)`, while `(f 3)^2` squares the call's result. `f -3` is subtraction;
use `f(-3)` for a negative argument. `x=1,2` assigns 1 and returns a Sequence;
`x=(1,2)` assigns that Sequence. Semicolons are statement/block separators,
not another ordinary arithmetic precedence row.

## Binding, effects, and dispatch

Resolution is lexical and source ordered. `:=` introduces a cell before resolving
its initializer, supporting local recursion. Later declarations do not retarget
earlier references. `=` updates the selected cell or global binding. Blocks and
collection literals introduce no scope. Closures capture cell addresses, so
siblings from one factory share updates and separate factory invocations do not.
`local name` reuses a current-scope binding when present and returns its Symbol.

`x -> body` binds the whole operand, including a Sequence. `(x,y) -> body`
requires two arguments by unpacking a Sequence; a List remains one argument.
`return` exits the current invocation and preserves writes already performed.
Ordinary errors—including fuel exhaustion—roll back the whole worksheet input,
including captured-cell updates and new ring identities. Earlier inputs remain
committed. Failed inputs still advance the input number. Imports do not transfer
mutable worksheet state; persistent exported Lean declarations are separate.

Runtime operator behavior depends on operand classes. `==` can promote numeric
values; `===` preserves their tags. Polynomial operations check ring identity,
not just printed variable names. A polynomial right operand for `//` or `%`
supports single-term division; a `GroebnerBasis` right operand for `%` dispatches
to source `normalForm`. `normalForm(f, list)` performs ordered division by that
list, without first replacing it by its Gröbner basis. Matrix operations are the
restricted provenance interface linked above. Unsupported combinations produce
method/type errors rather than implicit conversion to unrelated domains.

## Execution is not proof coverage

| Facility | What its evidence establishes |
| --- | --- |
| Parser/runtime regressions and native comparisons | Particular examples and implementation boundaries; not general native-M2 equivalence. |
| Exported `.code` / `.definition` | A persistent representation and its definitional equation; not its mathematical contract. |
| `#m2_check` | Kernel-replayed equality for a particular source result. |
| Natural-number contracts and Lean handles | Soundness in their supported verification fragments. Runtime syntax can be broader: handle `wpV` excludes assignment, nested functions, return, and rings. [Verified functions](m2-verified-functions.md) |
| Intent contracts and proof jobs | Naming/approval/export/replay infrastructure. A selected contract or proposition definition is not itself a proved theorem. [Stage 1](m2-intent-stage1.md), [Stage 2](m2-proof-stage2.md) |
| Polynomial GCD | Separate total-correctness results for the stated univariate QQ domain and runtime assumptions. [GCD](m2-gcd.md) |

Additional mathematical theorems on other feature branches do not silently
expand the language grammar or these proof tactics. This reference does not
claim expert sign-off, general parser preservation, whole-language translation
correctness, or universal Buchberger correctness.

## Keeping the reference checked

[`MacauleanTest/LanguageReference.lean`](../MacauleanTest/LanguageReference.lean)
contains named kernel-checked anchors for precedence, binding order, captured
cells, arity, return, short circuiting, recursion/exhaustion, rollback, classes,
polynomial dispatch, provenance matrices, and representative rejection boundaries.
Run `lake build MacauleanTest.LanguageReference`; the normal `lake test` driver
also imports it. Existing topic-specific worksheet/import/native suites remain
the broader conformance evidence. Changes to scope should update this matrix,
the relevant detailed guide, and executable examples together. Rejection tests
must retain the distinction between unsupported dialect forms and invalid native
syntax; an implementation bug is not an intentional restriction until specified.
