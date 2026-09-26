# Identifier binding is not keyword quotation

The functions/lexical-binding fragment implements `local name` for identifier
names, including its Symbol result and shared lexical cell. It does not implement
M2's separate Keyword values or quotation of keyword tokens.

This distinction matters for inputs that superficially look malformed:

| Native M2 source | Native interpretation |
| --- | --- |
| `local +` | The Keyword `+` |
| `local if` | The Keyword `if` |
| `local;` | The Keyword `;`, not a declaration followed by a semicolon |
| `local` at EOF | The Keyword representing the end-of-file token |
| `f=(x,y)->(local; x)` | A valid function containing application of the quoted semicolon |

Defining that last function succeeds natively; calling it with `(2,3)` fails.
It is wrong to classify its definition as malformed syntax merely because this
interpreter does not yet model Keywords. It is equally wrong to implement bare
`local` by inventing an anonymous variable or returning null.

The current frontend rejects these forms because `local` requires an identifier
in this fragment. `FunctionCases.invalidSyntax` contains only independently
native-rejected syntax/binders. `unsupportedKeywordQuotes` contains native-valid
keyword quotations and is tested separately by `FunctionLocalReference.lean`:

- kernel, input-reader, and actual DSL-category checks retain the frontend's
  rejection of unsupported forms;
- native checks assert Keyword class and exact spelling before serialization;
- the function case checks both successful construction and its native
  `LocalQuote` subtree, rather than treating an unsupported closure wire value
  as an error in the language.

These boundaries do not restrict ordinary `local x`, `x := value`, lexical
captures, local recursion, or the use of identifier Symbols returned by `local`.
They reserve first-class keyword/operator quotation for the symbolic-language
extension. See [functions and lexical binding](m2-functions.md) for the implemented
runtime and [the executable worksheet](../MacauleanTest/InterpreterFunctionsDSL.lean)
for examples.
