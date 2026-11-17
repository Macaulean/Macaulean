# Runtime bindings in the reduction proof targets

The generic `m2gbReduce` representation and irreducibility targets now require
`Runtime.PreludeBindings s`: every protected name resolves to the value it has
in the production prelude. This includes recursively called library helpers and
polynomial primitives. User globals, extra bindings, and arbitrary heap data
remain permitted.

This is necessary even when the initial call directly names the library object.
The source program resolves its recursive calls through the runtime environment.
Without the condition, a state can bind `m2gbReduce` to a closure returning the
integer `7`. Starting from a valid one-generator representation and an empty
reducer list, the library executes a move step and then calls that closure. The
result is an integer rather than the required polynomial/row pair.

`MacauleanTest.RuntimeEnvironment` preserves the old unrestricted representation
and irreducibility targets and proves both false using this actual-runtime counterexample. It also
checks that `PreludeBindings` rejects the state. This does not describe a normal
worksheet escape: the interpreter already protects these names against writes.
The missing restriction was in a proposition quantified over arbitrary states.

`checkPreludeBindings` computes a Boolean check. Its equivalence theorem and
`PreludeBindings.of_check` let concrete snapshots discharge the hypothesis with
`by decide +kernel`; a Boolean result is never trusted without that theorem.

The new invariant holds in the initial runtime state and is preserved by call
frame allocation, function allocation, successful single or multiple assignment,
and any transition known to preserve the environment. A user-global assignment
regression ensures the condition does not pin the entire environment. The proofs
use the existing `checkWritable` behavior; interpreter semantics are unchanged.

These lemmas are prerequisites for the [source reduction representation
proof](m2-reduction-proof.md), which now discharges both `RepresentationStatement` and `IrreducibleStatement`.
The environment lemmas alone do not establish preservation through every evaluator
construct or either mathematical reduction target. The correction does not
approve a contract or install an algorithm-correctness theorem.

Dependency: based on #49 and its existing DSL stack, independent of the row
correctness and representation PRs #52/#53. Validation is part of the ordinary
`lake test` driver, including transitive axiom checks on the new lemmas and
counterexample. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
