# Named Lean definitions from M2 worksheets

Import `Macaulean.Interpreter.DSL` and write ordinary M2 under `open M2`.
Successful inputs automatically expose their new or changed visible bindings as
compiled Lean definitions. No additional export command or verification import is
required. See the executable [example](../Examples/DefinitionExposure.lean).

```lean
import Macaulean.Interpreter.DSL

namespace Demo
open M2

answer = 42;
square = x -> x*x;
gcd2 = (a,b) -> if b == 0 then a else gcd2(b,a%b);

example : M2Generated.answer = (42 : Int) := rfl
#eval (M2Generated.square 64 (.zz 5)).map Prod.fst
example : (M2Generated.gcd2 128 (.sequence [.zz 48,.zz 18])).map Prod.fst =
    .ok (.zz 6) := by decide

#m2_definition "gcd2"
#print M2Generated.gcd2
#print M2Generated.gcd2.code
#check M2Generated.gcd2.definition
end Demo
```

## Names, revisions, and inspection

Within `namespace Demo`, the first export of `square` is
`Demo.M2Generated.square`. Outside a namespace, the Lean module name supplies the
prefix instead. Use an explicit namespace for stable, short names in a worksheet.
Generated names have declaration locations and documentation, so ordinary Lean
hover and go-to-definition work.

`#m2_definition "square"` reports the latest export in the current worksheet and
prints inspection commands. It does not evaluate the function. Each export has:

| Declaration | Meaning |
| --- | --- |
| `square` | A callable Lean definition, or native Lean data for a data binding. |
| `square.value` | The exact tagged M2 runtime value. |
| `square.state` | The immutable runtime snapshot containing its globals, heap, and captured cells. |
| `square.code` | The lowered lambda for ordinary closures and library functions; otherwise the lowered input that produced the export. |
| `square.definition` | A kernel-checked definitional equation for the exported Lean definition. |
| `answer.value_eq` | For data exports, a kernel-checked equation encoding the native Lean data back into the exact runtime value. |

Reassignments create `answer.v2`, `answer.v3`, etc., with the same metadata and
proofs beneath each name. `answer` always denotes its first exported version.
These names are not mutable aliases. Use `#m2_definition` to discover the current
revision rather than predicting its number. The binding's original export
namespace remains its namespace across later assignments.

A change anywhere in runtime state also refreshes previously exported functions,
symbols, and collections containing handles. This conservative policy captures
changes to dependencies even if a function's own handle did not change. An
unrelated assignment can therefore advance a function's revision. Data without
handles is refreshed only when its visible value changes. Reassigning exactly the
same data does not create another version.

Generated definitions survive module imports. The live M2 session and the
latest-revision registry remain file-local. Imported exports are referenced by
their ordinary Lean names; importing a worksheet does not populate a new M2
session with its variables. Resetting a session does not erase old declarations.
Reserve the generated namespaces: a name collision is reported as an error, with
no partial export or worksheet binding committed.

## Native values and functions

| M2 binding | Type of the main Lean export |
| --- | --- |
| Integer | `Int` |
| Rational | `Rat` |
| Boolean | `Bool` |
| List or sequence | `List Value`; `.value` preserves the original tag. |
| Polynomial ring | `Polynomials.RingInfo` |
| QQ polynomial | `Macaulean.Polynomial Rat n`, where `n` is its ring's variable count. |
| Callable value | `Nat → Value → Except Error (Value × Runtime.State)` |
| Other values | `Value` |

Polynomial `.value_eq` records the original ring identity as well as the encoded
polynomial. The native polynomial type alone does not distinguish two different
runtime rings with the same number of variables. Use `.value` and `.state` when
calling the interpreter, and keep ring identities in mathematical specifications.
These are the project's polynomial types, not Mathlib's `MvPolynomial`.

Functions keep M2's dynamic dispatch and argument conventions: pass `.zz 5` for
an integer, `.sequence [a,b]` for two arguments, and `.sequence []` for no arguments.
The fuel argument bounds interpreter depth. Insufficient fuel returns an error.
Calling an export starts from its frozen state and never mutates the worksheet.
The result includes the new runtime state, which is necessary for effects and
returned handles. For example:

```lean
makeAdder = x -> y -> x+y;

def useAdder : Except Macaulean.M2.Error Macaulean.M2.Value := do
  let (fn,state) ← M2Generated.makeAdder 64 (.zz 10)
  let (result,_) ← Macaulean.M2.Runtime.finish
    (Macaulean.M2.Runtime.call 64 fn (.zz 3) state)
  return result

example : useAdder = .ok (.zz 13) := by decide
```

Use `.map Prod.fst` when you only need a data result. Do not detach a closure or
symbol from its corresponding state, or mix handles from unrelated snapshots.
An exported `.value` is meaningful with its accompanying `.state`.

## What is proved

The generated equations are ordinary Lean theorems checked by the kernel. Data
round-trip equations connect native exports to tagged runtime values. Function
equations connect exported calls to `DefinitionExposure.run`, which executes the
actual `Runtime.call` interpreter against the captured state. The exporter does
not run function bodies to generate these equations, nor add assumed contracts.
Concrete computation examples can be proved with kernel reduction, as above.

This exposes the existing interpreter semantics as persistent Lean declarations.
It does not yet translate arbitrary M2 algorithms into standalone typed recursive
Lean algorithms, establish equivalence with native Macaulay2, automatically prove
termination, or prove that an algorithm satisfies a universal mathematical
specification. Those require additional specifications and proofs. In particular,
the GCD example above proves a concrete result, not universal GCD correctness.

The feature covers bindings supported by this DSL, including captured functions,
compositions, library aliases, side-effect-created bindings, ring generators, and
collections. It does not add support for language features absent from the DSL.
Bare expressions without changed bindings keep their existing output behavior.
Full snapshots and conservative function revisions cost elaboration time and
artifact space. Exports share snapshots within each input and reuse identical
closed literals across revisions. Large lists are split into compiled chunks so
heap exports do not require raising the compiler recursion limit. Proofs of large
computations may still require the usual Lean heartbeat or reduction limits to be
increased.

## Verification

```sh
lake build MacauleanTest.DefinitionExposureImport MacauleanTest.DefinitionExposureVerification
lake env lean Examples/DefinitionExposure.lean
lake test
python3 scripts/intent-lsp-test.py
```

Tests cover native data, polynomial round trips, compiled and kernel execution,
recursive GCD, fuel errors, mutable captures, returned closures, immutable
revisions, import isolation, generated theorem dependencies, source locations,
name-collision rollback, session reset, and the verification frontend. The real
Lean editor test checks generated-name hover, go-to-definition, callable proofs,
and replay after editing a worksheet.
