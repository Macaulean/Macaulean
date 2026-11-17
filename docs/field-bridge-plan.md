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

Upstream baseline: 0964f3c. Lean: 4.33.1. The baseline had no Mathlib dependency.
The proof-only `MacauleanMathlib` library now pins Mathlib v4.33.1; the interpreter
and existing executable certificate modules do not import it.
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

## Implemented checkpoints

* `MathematicalViews` and `MathematicalExport`: shared field/ring/polynomial/ideal
  exports over QQ and checked prime fields, exact snapshot decoding theorems,
  stable names after reassignment, and round-trip/foreign-ring/malformed-dimension
  tests. These supersede the initial QQ-only `IdealView` checkpoint.
* `Algebra.PrimeField`: canonical modular residues with a standard
  `Lean.Grind.Field` instance derived from an exhaustive inverse-law check.
  Small prime characteristics pass; composite characteristics fail. This first
  checker is intentionally for small primes and is not a fast primality test.
* `KernelPolynomial` and its weighted-observation proofs are generalized from
  Rat to commutative coefficient rings. Existing QQ coefficient/runtime proofs
  still build.
* `Algebra.Polynomial`: coefficientwise meanings, generic arithmetic soundness,
  ideals closed under equivalence/addition/multiplication, and their generated
  ideals with the least-ideal theorem.
* `Algebra.CoefficientField` packages QQ and checked prime fields.
  `FinitePolynomialData` validates canonical residue/exponent encodings and
  proves decode/encode and arithmetic bridge identities.
* `PrimeFieldAlgebra` proves the requested membership example over F_5 at the
  mathematical layer and distinguishes x^5-x from zero as a formal polynomial.
* `FiniteObjects` and `FiniteOps` connect GF(p), modular scalar and polynomial
  arithmetic, ideals, matrices, and basis containers to the ordinary worksheet
  runtime. The existing M2 reduction/Buchberger source runs over these fields.
* `MathematicalExport` tests now prove the membership example from actual
  worksheet exports over QQ and F_5. The exported ideals use the common generated
  ideal semantics, and field exports provide standard Lean field instances.
* `FiniteFieldWorksheet` checks execution, provenance, characteristic rejection,
  ring separation, and rational promotion. `FiniteFieldsM2` compares exact
  coefficients against native M2 for nine bases and nine remainders.
* `Algebra.Certificates` proves soundness of dimension-checked polynomial
  representation rows and two-way ideal-equality certificates over every supported
  coefficient ring. `CertificateCommands` uses source-language basis/reduction
  code only to propose data, then emits kernel-checked membership/equality theorems.
  Tests cover QQ/F_5 examples, F_3 zero/unit ideals, import persistence, malformed
  rows, insufficient one-way containment, and incompatible coefficient fields.

* `MacauleanMathlib`: standard multivariate-polynomial interpretation with
  coefficient preservation and arithmetic soundness; a well-founded grevlex
  monomial order proved to match the runtime comparator; the licensed Buchberger
  criterion adapted from WuProver/groebner_proj, with provenance and standard-axiom
  audit; and a finite indexed bounded-representation interface implying the actual
  leading-term-ideal Gröbner property. The executable checker and commands below
  use this interface.

* `GroebnerCertificates`, `GroebnerChecker`, and `GroebnerViews`: executable
  leading-term, monicity, degree-bound, square S-pair matrix, and representation
  checks with a kernel-checked theorem that the candidate is a Gröbner basis of
  the original ideal. The identity-only/non-Gröbner negative example is rejected.
* `#m2_groebner` publishes that theorem from the actual worksheet snapshot.
  QQ, F_5 with nonmonic input, F_2, zero/unit ideals, malformed evidence,
  cross-field rejection, and theorem import persistence are covered.
* `#m2_import` accepts closed fields/rings/polynomials/finite ideal presentations,
  kernel-checks the evaluated encoding before publication, reserves ring identities,
  and rejects conflicting identities/protected names atomically. End-to-end QQ/F_5
  tests create ideals in Lean, import them, compute/certify their bases, and export
  the identical presentations back to Lean. `Examples/FieldIdealBridge.lean` is a
  complete checked user example.

Pending delivery: integrate current upstream, run the final combined regression
suite and examples, audit the acceptance items above, and open the upstream PR.

Validation at the finite-field worksheet checkpoint: `lake build MacauleanTest`
passed (394 jobs). This includes the new finite native comparisons and import
tests, the existing rational interpreter/kernel corpus, existing native M2
polynomial and Gröbner comparisons, and function-contract/handle regressions.
The exported equality and membership theorem axiom checks contain only standard
Lean axioms. Existing repository warnings and intentional negative-control
`sorry` tests remain unchanged.

Validation at the mathematical-theory checkpoint: the combined existing suite
and `MacauleanMathlibTest` passed (9127 jobs), followed by the additional
worksheet ideal-equality transport test. The theory tests check actual exported
QQ/F_5 membership proofs, finite-field ideal-equality transport, grevlex-vs-lex
ordering, the general well-foundedness instance, empty and unit basis certificates,
and standard-axiom audits. `MacauleanTest` imports this suite so `lake test` covers it.
These mathematical-theory checks are now complemented by the executable checker
and worksheet command tests listed above.

After the combined import exposed a root-name collision, the existing core
factorization predicates were moved into `Macaulean.Factorization`; their tactic
and negative-control tests pass. A fresh `lake test` then passed all 9125 targets,
including the native polynomial comparisons and the root importing both libraries.
