# Field, ideal, and Gröbner bridge implementation plan

The acceptance scope is rational and prime-field polynomial worksheets with
stable mathematical exports, certified Gröbner bases, and usable membership
proofs. Extension fields are a documented follow-up. This file tracks work;
it is not a declaration that the features below are implemented.

## Required end-to-end behavior

* Construct fields, polynomial rings, polynomials, ideals, and candidate bases
  using the worksheet DSL, over QQ and prime fields.
* Export actual worksheet values to immutable Lean declarations, retaining
  coefficient field, ring identity, variable ordering, and grevlex ordering.
* Interpret polynomial equality coefficientwise, not by evaluation at field
  elements (which is insufficient over finite fields).
* Prove that a certified basis generates the original ideal and satisfies the
  Gröbner property for the declared order. A runtime basis tag is not evidence.
* Check representation and S-polynomial evidence with kernel-checked soundness
  theorems, without sorry, additional axioms, or native_decide.
* Demonstrate membership of x^3-1 in (x^2-y, x*y-1), over QQ and F_5.
* Support explicit Lean polynomial/generator-list inputs and prove round trips.
* Reject invalid characteristics, incompatible rings, malformed dimensions,
  bad certificates, and unsupported objects; preserve existing QQ behavior.
* Document syntax, guarantees, limitations, and examples; run the relevant
  existing regressions and new positive/negative checks; open an upstream PR.

## Repository constraints discovered

Upstream baseline: 0964f3c. Lean: 4.33.1. There is no Mathlib dependency.
The current runtime and arithmetic proofs use Rat coefficients. Existing
`Verification.Views` supplies ring-indexed polynomials, coefficientwise
equivalence, and representation rows. Definition exposure already produces
immutable runtime snapshots, so mathematical export should reuse those snapshots.
The separate reduction-correctness worktree has additional ideal-membership
proofs; avoid modifying it or silently depending on unmerged declarations.

## Implementation sequence

1. Typed ideal views, exact decoding/encoding proofs, and worksheet exports.
2. Coefficient-field representation and executable prime-field arithmetic,
   including evidence that accepted characteristics define fields.
3. Field-generic polynomial semantics and arithmetic soundness.
4. Ideal and Gröbner certificate semantics, checking, and soundness.
5. Worksheet certification commands, bidirectional examples, regressions,
   documentation, and upstream PR.

The sequence is an implementation order, not a reduction of the acceptance scope.
