# Univariate GCD and input-derived fuel

```lean
import Macaulean.Interpreter.DSL
open M2

R = QQ[x];
gcd(x^4-1,x^3-1)
-- x - 1 : QQ[x]
```

`GCD.m2` contains the Euclidean algorithm. It calls the existing M2-source
`normalForm` and returns a monic answer, with `gcd(0_R,0_R) = 0_R`.
Both arguments must be polynomials in the same one-variable QQ ring.
Integers, scalar/polynomial mixtures, multivariate rings, zero-variable rings,
and distinct ring identities are rejected. This is deliberately narrower than
native M2's overloaded `gcd`. Native answers are compared after monic
normalization in the differential tests.

The source is compiled with the ordinary M2 parser and lexical resolver.
GCD calls use the same pure interpreter as other library functions.
No native M2 call or separate production Lean GCD algorithm is involved.

## Input-derived execution budget

The Lean API `Macaulean.M2.GCD.compute f g` accepts two `Value`s, validates and
normalizes them, and invokes the M2-source function with:

```
128 * (max (degree f) (degree g) + 4)
```

Here zero has natural degree zero. Degree is measured after normalization,
so duplicate or zero terms cannot artificially inflate the budget.
The API runs in a fresh runtime state and preserves the input ring identity.
The bound is proved sufficient for every input accepted by the production
validator in `GCD/ComputeCorrectness.lean`. The proof includes source validation,
normal-form execution, Euclidean recursion, and monic normalization. Invalid
inputs still return validation errors.

Ordinary worksheet `gcd(f,g)` now receives the same automatic degree budget.
The evaluator recognizes the function value, including aliases, higher-order
calls, and calls inside closures. `m2.maxDepth` still limits the surrounding
worksheet execution; a GCD call that is reached runs the checked-in source with
its proved budget in the caller's state. Validation errors still roll back the
worksheet input. Explicit `Runtime.call` and `runWithFuel` retain bounded
execution by default.

## Total-correctness proof status

`Macaulean.Interpreter.GCD.TotalCorrectness` proves `degree_bound_total`:
given the stated remainder, divisibility, normalization, and rank laws,
the abstract Euclidean loop returns a normalized GCD in
`max (degree f) (degree g) + 2` calls. This includes the terminating base call.
Its conclusion includes both divisibilities and the universal common-divisor
property. There are no added axioms or proof holes.

The concrete algebraic prerequisites now have kernel-checked proofs:

- `GCD/Univariate.lean` proves that the production normalizer produces nonzero
  terms in strictly decreasing degree order, preserves degree bounds, and is
  idempotent. Canonical polynomials are equal when all coefficients agree.
  `cancellation_rank_lt` proves that leading-term cancellation using the actual
  multiplication and subtraction operations decreases degree. `sub_head_rank_lt`
  covers removal of an irreducible leading term, the other reduction branch.
- `GCD/Arithmetic.lean` connects the actual DSL subtraction, multiplication,
  leading-coefficient, leading-monomial, and monomial-quotient operations to this
  representation, for arbitrary ring identities and polynomial inputs.
- `GCD/Algebra.lean` proves polynomial multiplication identities coefficientwise
  and proves `common_divisors_sub`: replacing `f` by `f-q*g` preserves exactly
  the common divisors with `g`. Divisibility carries a polynomial quotient witness.
- `GCD/Normalization.lean` proves that the production scalar normalization
  preserves divisibility in both directions and returns a monic polynomial or
  zero. It also connects actual scalar division and zero tests in the DSL to
  these operations.
- `GCD/Execution.lean` proves the actual source GCD base cases, both branches
  of the singleton-divisor selector, and the empty coefficient-row update.
  The statements include evaluator budgets and the resulting runtime states;
  kernel equality identifies each body with the compiled M2 source.
  Its `gcd_step` theorem also composes successful normal-form and recursive
  calls into the source GCD recursive branch, with exact evaluator-depth
  offsets. The whole-loop theorem below discharges the nested-call obligations.
- `GCD/Frames.lean` proves that allocating helper frames and writing their
  private cells preserve existing caller cells and globals, including
  successful reads through lexical references. It tracks the current function's
  locals across nested calls and proves that local writes update the tracked
  values.
- `GCD/Reduction.lean` identifies the compiled `m2gbReduce` body and proves
  its zero-input base case. It also proves execution of the branch that moves
  the leading term into the remainder, conditional on success of the recursive
  call: the pending polynomial becomes its tail and the accumulator receives
  the leading term through the actual DSL arithmetic.
  The cancellation branch now has a corresponding execution proof, including
  computation of the cancellation multiple, writes to local variables, and
  the nested empty coefficient-row update. The dispatch theorem connects
  selector execution to either branch.
- `GCD/ReductionSteps.lean` constructs the intermediate states for both branches
  and proves preservation of the caller's state.
- `GCD/ReductionTotal.lean` proves successful execution of the actual reduction
  source for every canonical univariate input and nonzero singleton divisor.
  A sufficient evaluator-depth budget is `64 * (rank input + 1)`, where rank
  is zero for the zero polynomial and degree plus one otherwise.
- `GCD/ReductionCorrectness.lean` proves `reduction_correct`: the source call
  succeeds within that bound, returns a canonical remainder whose terms have
  degree strictly below the divisor, and preserves exactly the common
  divisors. The proof includes the whole recursive reduction, with zero initial
  accumulator and empty coefficient rows.
- `GCD/NormalFormPrimitives.lean` and `GCD/BarePairs.lean` prove validation,
  promotion, zero-accumulator construction, and source divisor packaging for
  the normal-form inputs used by GCD.
- `GCD/NormalForm.lean` proves `normal_form_correct` for the complete source
  `normalForm` call with a nonzero singleton divisor. It includes successful
  execution, preservation of caller state, a canonical remainder strictly below
  the divisor's degree, and preservation of common divisors. A sufficient
  depth budget is `64 * (rank input + 1) + 100`.

- `GCD/LoopCorrectness.lean` proves total correctness of the actual source
  Euclidean loop, including all zero cases and monic normalization.
- `GCD/Interface.lean` connects the public `gcd` source entry point to that loop.
- `GCD/ComputeCorrectness.lean` proves `compute_total`: every input accepted by
  `gcdInputs` succeeds with the automatic degree-derived budget and returns a
  canonical monic-or-zero GCD of the validated polynomials. Validation is proved
  to produce canonical representations, including for raw noncanonical inputs.

The GCD tests audit these theorem dependencies to reject proof holes and
unapproved axioms. The actual source algorithm and the `GCD.compute` API now
have total-correctness proofs for the supported univariate QQ domain.

`GCD/AutomaticCorrectness.lean` proves that the worksheet handler executes that
same source with its sufficient budget and preserves the caller's state prefix.
The evaluator remains structurally recursive; the handler invokes the bounded
source evaluator, without recursively reinstalling the handler.

## Reusable worksheet certificates

The public verification import exposes a command that creates an ordinary Lean
theorem about the exact values of three worksheet bindings:

```lean
import Macaulean.Verification
set_option maxRecDepth 50000
set_option maxHeartbeats 30000000
open M2

R = QQ[x];
f = x^4-1;
g = x^3-1;
d = gcd(f,g);
#m2_gcd_proof resultProof "f" "g" "d"
#check resultProof
#print axioms resultProof
```

`resultProof` has type `Macaulean.M2.GCD.ValueSpec fValue gValue dValue`,
where the values are embedded snapshots, not mutable worksheet names.
`ValueSpec` states successful input validation, canonical input and output
representations, preserved ring identity, monic-or-zero output, and the full
GCD property (both divisibilities and every common divisor dividing the result).
The theorem remains usable after any of the bindings change.

`GCD.certify_result` derives this statement from the universal `compute_total`
theorem and a computation equality. The command supplies that equality by
reflexivity, checked by Lean's kernel; its preliminary executable comparison
only provides diagnostics. Unknown bindings, invalid inputs, and wrong results
are rejected without installing a theorem. Large concrete certificates may
require higher Lean elaboration/kernel resource limits.

Tests cover explicit answers, kernel execution with the degree-derived budget,
native M2 comparisons, zero and constant inputs, rational coefficients, ring
checks, first-class functions, long divisions, and long Euclidean chains.
The universal guarantees come from the audited Lean theorems, not these tests.

```sh
lake build MacauleanTest.GCD MacauleanTest.GCDCertificates MacauleanTest.GCDM2 Macaulean.Verification.Fuel
lake test
```

## Requirement audit

| Requirement | Universal proof or regression gate |
| --- | --- |
| Same-ring univariate QQ domain, including raw noncanonical inputs | `validated_has_canonical` and `compute_total`; validation rejection tests in `MacauleanTest.GCD` |
| Zero, constant, rational and monic normalization cases | `monicNormalize_monic`, divisibility normalization lemmas and `gcd_loop_total`; exact and native cases |
| Execution of the checked-in M2 algorithm | Kernel equalities `gcd_entry_source`, `gcd_source`, `normal_form_source`, `reduction_source`; composed execution theorems |
| Fuel derived from normalized input degrees | `input_fuel_sufficient` and `compute_total`, with no caller-supplied fuel hypothesis |
| Automatic nested and first-class worksheet calls | `automatic_call_eq` and `automatic_call_correct`; depth-64 degree-1024 direct, alias, higher-order and nested closure tests, including actual `open M2` commands |
| Caller state preservation | `Extends`, frame lemmas and `automatic_call_correct`; caller-local retention regression |
| Reusable result certificates through the public import | `certify_result`; `MacauleanTest.GCDCertificates` checks exact theorem types, rejected declarations and snapshots after mutation |
| No proof holes or new axioms | Dependency audits permit only `propext`, `Classical.choice`, and `Quot.sound`, including generated certificates |
| Bounded runtime compatibility and native agreement | `Macaulean.Verification.Fuel`, explicit exhaustion controls, native M2 comparisons and the full `lake test` suite |

The automatic-call theorem assumes the standard library globals in the caller
state. Worksheet globals for these library functions are protected; local
bindings do not replace them. Its depth condition is that evaluation has reached
the GCD call with positive remaining depth. It does not assert termination of
arbitrary surrounding worksheet code.
