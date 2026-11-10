# Executed polynomial coefficient-row subtraction

`Macaulean.Verification.PolynomialRows.execute` specializes the generic source
execution theorem from PR #49 to arbitrary polynomial rows in a common ring.
For rows of dimension `n`, the actual `m2gbSubtractRow` library call succeeds at
depth `spare + 16*(n+1)`. Its result has dimension `n`, and each output entry has
coefficient `x.coeff powers - productCoefficient c y powers`. The convolution
specification is independent of production multiplication. Inputs may contain
unsorted terms, duplicates, and explicit zeros.

The theorem requires the recursive helper's global binding to refer to the
library function. It preserves globals, existing cells, function objects, and
the next ring identifier; fresh invocation frames remain in the append-only
heap. It uses the parsed/resolved library body equality in `RowProgram.source_body`
and the production arithmetic theorems, without assuming arithmetic correctness.

Import `Macaulean.Verification.PolynomialRows` for the small proof API, or
`Macaulean.Verification` for the worksheet frontend as well. `Subtracts` expresses
the pointwise coefficient specification, `construct` supplies successful
production operations, and `execute` connects these to the source interpreter.

Validation is in `MacauleanTest.PolynomialRows`: actual source execution with
noncanonical inputs, rational scaling and cancellation; a generic empty-row
execution theorem; wrong-dimension rejection; and transitive axiom audits.

`Macaulean.Verification.RowRepresentation.execute_represents` completes the
linear-combination part: if the two input rows represent `p` and `q` in the
same original generators, the returned row represents `p - c*q`. It uses the
existing coefficientwise `Views.Represents` relation. No independence,
nonzero-generator, nonempty-row, or canonical-representation assumption is
needed.

The supporting `PolynomialObservations` module proves that coefficientwise
equality determines arbitrary weighted sums, and proves multiplication
associativity for those observations. `linearPolynomial_coeff` connects the
finite polynomial sum to the original `linearCoefficient` specification.
`Subtracts.weighted` and `Subtracts.represents` lift pointwise subtraction to
whole rows; `execute_represents` then uses the actual source execution theorem.

The subsequent [source reduction proofs](m2-reduction-proof.md) establish the
full `m2gbReduce` representation invariant and remainder irreducibility. This
row-update theorem alone does not establish those results. Termination and
Buchberger correctness remain separate work.

Dependency: PR #49 (generic row execution), including #47/#48 and #41's existing
stack. The branch retains those dependencies so that its incremental diff is
reviewable; retarget after the parent stack lands.

The representation follow-up is stacked on PR #52 (the dimension and pointwise
coefficient theorem). Its tests are in `MacauleanTest.RowRepresentation`, with
15 transitive theorem-dependency audits, a generic source representation theorem,
and noncanonical/canceling coefficient and empty-generator regressions.
