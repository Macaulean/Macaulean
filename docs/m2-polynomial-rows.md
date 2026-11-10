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

This is the dimension and pointwise arithmetic part of the coefficient-row
milestone. Preservation of a row's linear combination still needs convolution
linearity and associativity. The full `m2gbReduce` representation invariant,
irreducibility, termination, and Buchberger correctness remain separate work.

Dependency: PR #49 (generic row execution), including #47/#48 and #41's existing
stack. The branch retains those dependencies so that its incremental diff is
reviewable; retarget after the parent stack lands.
