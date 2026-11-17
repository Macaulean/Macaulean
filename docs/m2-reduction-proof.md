# Source reduction representation and irreducibility

`ReductionRepresentation.representation` proves the exact
`RuntimeReduction.RepresentationStatement` for the tracked four-argument
`m2gbReduce` source helper. It is available from `Macaulean.Verification`.

Given same-ring generators, a dimension-indexed coefficient row, represented
reducers, and an initial coefficientwise equation
`pending + remainder = row · generators`, every successful runtime call returns
a polynomial and a row of the original dimension with
`returned remainder = returned row · generators`. The runtime state must retain
the production protected prelude bindings. Inputs need not be normalized,
univariate, or nonzero, and reducers need not form a Gröbner basis.

The proof follows the actual tracked source AST by strong induction on evaluation
fuel. Source-body identities, evaluator arithmetic, indexing, private assignments,
and helper calls are checked; no alternative reduction algorithm is assumed.
Each recursive branch exposes a call at a strictly smaller original budget.

`ReductionIrreducibility.irreducible` also proves the exact
`RuntimeReduction.IrreducibleStatement`: when the initial remainder is
irreducible with respect to the supplied reducers, every successful call returns
an irreducible remainder. This theorem does not require the representation
invariant or any relationship between the input row and the pending polynomial.
It is also exported by `Macaulean.Verification`.

Both results concern successful returns. They do not prove successful termination
on every input or full Buchberger correctness. A zero reducer can still cause a
runtime error. No intent approval or proof-acceptance policy is changed.

Dependencies: this branch combines #53 (row linear-combination preservation,
which depends on #52) and #54 (protected-binding condition), on the #49 DSL
stack. `stack/dsl-row-and-environment` is their integration/review base, not a
separate feature to merge. #33/#34 are assumed as upstream prerequisites.

The checked foundations currently cover:

- `ReductionValues.eval_eq_zero` and `eq_zero_coefficients`: the interpreter's
  zero test implies zero at every coefficient, including noncanonical inputs.
- `ReductionValues.lead_term`: the production leading-term primitive produces a
  polynomial in the same ring and dimension.
- `ReductionValues.representation_zero`: the actual `m2gbReduce` zero branch
  satisfies the existing representation conclusion at every successful budget.
  It uses the source-body equality already proved in the GCD implementation and
  the evaluator's cross-budget uniqueness theorem.
- `ReductionMove.successful`: every successful move branch, at its original
  budget, exposes a recursive call at a strictly smaller budget. Its pending
  polynomial and remainder retain the input representation invariant and its
  state retains protected prelude bindings. The proof covers arbitrary rings,
  dimensions, and noncanonical polynomials. `execute` identifies the exact
  production call at depth `fuel + 7` from branch depth `fuel + 9`; the depth-8
  boundary is exhausted, and evaluation monotonicity excludes every lower depth.
- `ReductionDispatch.successful`: every successful nonzero source call reaches
  one of the two source branches at smaller fuel. The selector preserves the
  frame, assigning its result to the private slot preserves protected bindings,
  and only a Boolean comparison can reach a branch. No selector correctness
  hypothesis or extra nonzero-reducer restriction is assumed.
- `ReductionTypes`: successful leading-monomial and monomial-quotient primitives
  retain the input ring and exponent dimension. Leading coefficients are rational
  scalars, and rational scaling returns a same-ring polynomial. Successful reducer
  indexing selects an existing supplied reducer, including negative indices.
  Malformed dimensions and failed divisibility remain errors.
- `ExecutionEffects.evaluate`: expressions in the supported read-only fragment
  preserve existing cells and globals under explicit callee effect contracts.
  The fragment includes arithmetic, indexing, conditionals, sequencing,
  collections, and named global calls. It excludes assignments, early return,
  dynamic callees, and `%`'s special library dispatch.
- `ExecutionEffects.library_safe`: a tracked recursive library function in that
  fragment preserves caller cells and globals when its other callees are known
  production primitives. Recursive effects are proved by induction on the
  actual evaluation depth, rather than assumed as a self-contract.
- `ReductionEffects.selector_safe` and `row_safe`: the theorem instantiated on
  the actual `m2gbReducer` and `m2gbSubtractRow` bodies. These results hold for
  arbitrary input values and budgets; errors are allowed, but no return signal
  escapes the calls. Successful calls may append private cells.

The effects relation is the existing `GCD.Execution.Extends`: it concerns
original cells and globals, not equality of the entire heap or garbage collection.
Function allocation is permitted. The result is useful for preserving the
caller's current reduction frame across recursive search and row helpers.

Run `lake build MacauleanTest.ReductionFoundations` for the focused tests and
38 transitive axiom audits. The tests include noncanonical cancellation, a
selector that must skip a non-divisor, exact move fuel boundaries, caller-cell
retention, and rejection of
unsupported effect-checker syntax. Only `propext`, `Classical.choice`, and
`Quot.sound` are admitted by the audits.

`ReductionRow.successful` identifies the actual row helper result at any
successful budget and carries its representation and allocation effects.
`ReductionCoefficient.successful` proves that the source coefficient expression
returns a same-ring polynomial without changing state; `normal` excludes an
early-return signal. `ReductionCancel.successful` and `ReductionCancelTail.successful`
connect both private assignments, the row helper, and the decreasing recursive
call. The final theorem combines these with the zero and move branches.

`lake build MacauleanTest.ReductionRepresentation` checks the exact universal
target and a two-variable, two-column regression that skips a reducer, cancels
a term, then moves a term into the remainder from a noncanonical input. It also
checks the zero-reducer error boundary and audits all theorem dependencies.
The complete validation commands are `lake test` and `lake build`.

## Ordered selector and irreducibility

`ReducerSelection.condition_execute` and `step` expose the actual source
selector and its primitive calls, including errors. `negative` proves that a
negative selector result certifies rejection of every candidate in the searched
suffix. Its induction is on the remaining list length, so it does not assume
termination of the outer reduction. It preserves the supplied order and does not
replace the selector with a separate search algorithm.

`ReducerSelection.test_false` connects the production leading-monomial and
monomial-divisibility calls to the exponent vectors in `Views.Irreducible`.
Normalization and dimensions are checked; raw sparse inputs may contain duplicate
or zero terms. `negative_leading_term` then proves that a head moved into the
remainder is irreducible. `IrreducibleArithmetic.add` proves that adding it cannot
introduce a reducible monomial, even when coefficients cancel.

`ReductionDispatch.successful_selected` retains the selector's actual call
result. The `successful_step` lemmas in the move, row, cancellation-tail and
cancellation modules expose execution facts without representation premises.
The original representation-preserving lemmas remain wrappers around these
facts. The final irreducibility proof follows the same decreasing runtime fuel:
zero returns the current remainder, cancellation preserves it, and movement adds
an irreducible head.

`lake build MacauleanTest.ReductionIrreducibility` checks the exact universal
target, six concrete regressions, and nine transitive axiom audits. Regressions
cover multiple selector rejections, a later divisor, noncanonical inputs,
nonzero initial remainders with unrelated input rows, empty reducer lists and
zero-reducer errors. No `sorryAx` or native-evaluation axiom is permitted.

This extension is stacked on the source representation proof (#55), which
carries the row and protected-environment dependencies described above. It does
not depend on the separate local-state handle extension (#58).

Next mathematical work: a DSL-facing ideal-membership corollary and full
termination as separate obligations. The representation equation alone does not
establish arbitrary `f - remainder` ideal membership from an unrelated initial
row; that needs an offset invariant or another explicit argument.
