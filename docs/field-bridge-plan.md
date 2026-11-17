# Field, ideal, and Gröbner bridge implementation plan

The acceptance scope is rational and prime-field polynomial worksheets with
stable mathematical exports, certified Gröbner bases, and usable membership
proofs. Extension fields are a documented follow-up. This file records the acceptance requirements and their implementation evidence.

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

## Implementation evidence

| Requirement | Implementation | Regression evidence |
| --- | --- | --- |
| QQ and prime-field worksheets | `PrimeField`, `CoefficientField`, `FiniteOps`, shared `Runtime` | `PrimeFieldAlgebra`, `FiniteFieldWorksheet`, `FiniteFieldsM2` |
| Immutable mathematical exports | `MathematicalViews`, `MathematicalExport` | `MathematicalExport`, `MathematicalExportImport` |
| Coefficientwise polynomial/ideal meaning | `Algebra.Polynomial`, `MacauleanMathlib.Polynomial`, `Worksheet` | finite-field x^5-x counterexample; transported worksheet proofs |
| Two-way ideal equality and membership | `Algebra.Certificates`, `CertificateCommands` | `CertificateCommands`, `CertificateCommandsImport` |
| Actual Gröbner property of the original ideal | `GroebnerChecker.checkBasis_sound`, `GroebnerViews.checkGroebner_sound` | `MacauleanMathlibTest/GroebnerCommands.lean`; standard-axiom audits |
| Matching well-founded grevlex order | `Grevlex.grevlexOrder`, `grevlexOrder_lt_iff` | grevlex-vs-lex example and general well-foundedness instance |
| Explicit reverse imports and round trips | `MathematicalImport`, decoder/encoder round-trip theorems | `MacauleanMathlibTest/MathematicalImport.lean` over QQ and F_5 |
| Rejection controls | dimensions, ring/field matching, inverse-law and degree-bound checks | malformed matrices, identity-only S-pair, cross-field, duplicate names, protected bindings, identity collisions |
| Usable documentation | `docs/field-bridge.md`, README link | `Examples/FieldIdealBridge.lean` |

The executable Gröbner checker validates leading terms, monicity, both dimensions
of the S-pair matrix, coefficient-row identities, and degree bounds. A correct
identity whose summands exceed the S-polynomial's degree is rejected. The root
certificate theorem identifies the original input ideal, not only the candidate's
own generated ideal. Successful worksheet executions and native comparisons are
additional regression checks, not the logical basis of certification.

The kernel checks imported runtime data against the encoding of the supplied
closed Lean term before any session mutation is published. Fresh ring identities
are reserved; conflicting identities and protected bindings fail atomically.
The reverse-direction tests create ideals from Lean data, import them, compute and
certify their Gröbner bases, and export the identical presentations back to Lean.

## Dependencies and compatibility

Lean remains at 4.33.1. The separate, non-precompiled `MacauleanMathlib` library pins
Mathlib v4.33.1. The core interpreter and membership/equality/import commands do
not import Mathlib. The licensed Buchberger proof and its dependency closure are
vendored with pinned provenance in `MacauleanMathlib/GroebnerTheory/README.md` and
an Apache 2.0 LICENSE. Axiom audits of the resulting certificates contain only
Lean's standard axioms.

The existing factorization predicates moved into `Macaulean.Factorization` to
avoid collisions with Mathlib's root names. Their positive and negative tactic
tests are preserved. The incoming row-proof, runtime-environment, and MRDI changes
from upstream through `b7ea4fe` are integrated; the combined test root retains both
upstream and bridge suites.

## Validation and delivery

Validation after integrating upstream `b7ea4fe`:

* `lake test`: passed all 9,148 targets, including the upstream row/MRDI/environment
  tests, native M2 comparisons, and the complete mathematical bridge suite.
* `lake build`: passed (281 jobs), including the default executable.
* `lake env lean Examples/FieldIdealBridge.lean`: passed with default options.
* Generated QQ/F_5 Gröbner theorem axiom guards: only `propext`, `Classical.choice`,
  and `Quot.sound`. Negative certificate and import controls also passed.
* `git diff --check`: clean.

The complete deliverable includes an upstream PR containing this implementation,
documentation, and validation evidence. Extension fields remain a follow-up;
this first bridge covers QQ and prime fields with the fixed grevlex order.
