# Coefficientwise arithmetic contracts

This completes step 1 of the ideal-membership roadmap: connect the DSL's
polynomial arithmetic to the exact coefficientwise views used by the existing
verification contracts. It follows PR #40's denotation proofs.

For example, the coefficient of `x*y` in a product must be the sum of all input
term products whose exponents add to `[1,1]`. The new theorems prove this for
arbitrary supported rational polynomials and every exponent query. They also
prove that normalization preserves all coefficients and that addition and
subtraction act coefficient by coefficient.

## Proof layers

- `Macaulean/Interpreter/KernelPolynomialWeights.lean` proves preservation of
  arbitrary linear observations of sparse term lists. It handles all insertion
  branches, cancellation, unsorted terms, duplicates, and explicit zeros.
- `Macaulean/Verification/CoefficientLaws.lean` specializes those results to the
  existing `Views.coefficient`, `Polynomial.coeff`, `productCoefficient`, and
  `Equivalent` definitions. Multiplication is proved equal to the independent
  finite convolution already defined in `Views`; the specification is not
  redefined to call the production multiplier. Normalizing either input leaves
  this convolution unchanged.
- `Macaulean/Verification/PolynomialArithmetic.lean` carries the coefficient
  laws through the real `evalBinOp` and lexical `Runtime.eval` implementations,
  including operand decoding and repeated normalization. The execution equations
  are shared with the original denotation proofs. No interpreter code or contract
  definition changes.

Inputs need no canonical-form hypothesis. Their type records their common ring
and exponent dimension, including zero-variable rings. Runtime theorems preserve
changes made by operand evaluation: the right operand sees the left operand's
state, and the arithmetic operator retains the final state.

## Using the results

The usual `Macaulean.Verification` import exposes these theorems. A smaller import
is sufficient for arithmetic proofs:

```lean
import Macaulean.Verification.PolynomialArithmetic
open Macaulean.M2 Macaulean.M2.Verification

example (p q out : Views.Polynomial r)
    (h : evalBinOp .mul p.value q.value = .ok out.value) :
    ∀ powers, out.coeff powers = Views.productCoefficient p q powers :=
  PolynomialArithmetic.successful_mul_coefficients p q out h

example (p q out : Views.Polynomial r)
    (h : evalBinOp .add p.value q.value = .ok out.value) :
    Views.Equivalent out ⟨KernelPolynomial.add p.data q.data⟩ :=
  PolynomialArithmetic.successful_add_equivalent p q out h
```

The main entry points are:

| Need | Theorems |
| --- | --- |
| Coefficients of production normalization/arithmetic | `Views.coeff_normalize`, `coeff_add`, `coeff_sub`, `coeff_mul` |
| Normalization preserves the existing equivalence relation | `Views.normalize_equivalent`, `PolynomialArithmetic.normalized_coefficients` |
| Actual operator returns a polynomial with the right coefficients | `PolynomialArithmetic.eval_add_coefficients`, `eval_sub_coefficients`, `eval_mul_coefficients` |
| Consume an existing successful operator equation | `PolynomialArithmetic.successful_add_coefficients`, `successful_sub_coefficients`, `successful_mul_coefficients` |
| Express the result through `Views.Equivalent` | `PolynomialArithmetic.successful_add_equivalent`, `successful_sub_equivalent`, `successful_mul_equivalent` |
| Lift through lexical evaluation, retaining state | `PolynomialArithmetic.runtime_add_coefficients`, `runtime_sub_coefficients`, `runtime_mul_coefficients` |
| Arithmetic balance of reduction updates | `PolynomialArithmetic.move_balance_coefficients`, `cancel_balance_coefficients` |

## Validation and boundaries

`lake build MacauleanTest.CoefficientArithmetic` checks the new tests; they also
run in `lake test`. They include noncanonical multivariate rational inputs,
normalization, addition, subtraction, convolution, a deliberately wrong
coefficient, cancellation to zero, zero-variable rings, and exponent queries of
other dimensions. A parsed-source example combines execution with its coefficient
specification. A theorem about arbitrary effectful operands checks runtime state
threading. Another theorem uses the existing `Views.Represents` relation to
express a successful multiplication as a one-generator linear combination.

Transitive axiom audits cover the public weighted-sum, view, operator, runtime,
and balance laws, plus the generic examples. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed. No proof hole or native-evaluation axiom is allowed.

The next milestone is dimension and representation preservation for the executed
`m2gbSubtractRow` helper. Then come the actual reduction loop's representation
invariant, leading-term selection and irreducibility, and an ideal-membership
proof exposed to DSL users. This change does not discharge
`RuntimeReduction.RepresentationStatement` or `IrreducibleStatement`, prove
termination, or certify Buchberger. It adds no new intent approvals or proof
acceptance rules.
