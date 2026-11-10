# Source reduction representation proof: work in progress

This branch combines the row-representation theorem from #53 and the corrected
runtime-environment hypotheses from #54. The complete
`RuntimeReduction.RepresentationStatement` is still an open obligation. No
complete reduction, irreducibility, termination, or Buchberger theorem is claimed.

The checked foundations currently cover:

- `ReductionValues.eval_eq_zero` and `eq_zero_coefficients`: the interpreter's
  zero test implies zero at every coefficient, including noncanonical inputs.
- `ReductionValues.lead_term`: the production leading-term primitive produces a
  polynomial in the same ring and dimension.
- `ReductionValues.representation_zero`: the actual `m2gbReduce` zero branch
  satisfies the existing representation conclusion at every successful budget.
  It uses the source-body equality already proved in the GCD implementation and
  the evaluator's cross-budget uniqueness theorem.
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
14 transitive axiom audits. The tests include noncanonical cancellation, a
selector that must skip a non-divisor, caller-cell retention, and rejection of
unsupported effect-checker syntax. Only `propext`, `Classical.choice`, and
`Quot.sound` are admitted by the audits.

Next: establish the move and cancellation branches against successful source
execution, thread their arithmetic/row invariants through the recursive call,
and assemble the universal representation theorem. Leading-term irreducibility
and full termination are subsequent, separate obligations.
