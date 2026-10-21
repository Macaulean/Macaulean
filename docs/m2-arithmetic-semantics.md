# Polynomial arithmetic: first reduction-correctness milestone

The DSL now has general algebraic laws for the polynomial arithmetic it actually
executes. These connect the kernel-evaluable implementation to
`Macaulean.Polynomial.denote`, the existing mathematical interpretation in the
project. Import `Macaulean.Verification.PolynomialArithmetic` directly, or use
the usual `Macaulean.Verification` entry point.

## What is proved

`Macaulean/Interpreter/KernelPolynomialSemantics.lean` proves that normalization
preserves denotation and that addition, subtraction, multiplication, and natural
powers have their expected meanings. The inputs can contain unsorted terms,
duplicate monomials, explicit zeros, and arbitrary rational coefficients. No
canonical-form assumption is needed, including for zero-variable rings.

`Macaulean/Verification/PolynomialArithmetic.lean` carries addition, subtraction,
and multiplication through the runtime's real `evalBinOp` implementation,
including its decoding and repeated normalization. Its `runtime_add`,
`runtime_sub`, and `runtime_mul` theorems lift those results to `Runtime.eval`.
Given successful operand evaluations, they establish a correctly typed output,
its algebraic meaning at every rational variable assignment, and the exact
resulting state. The right operand runs in the state left by the first operand;
the arithmetic operator preserves the state left by the second operand.

The public `successful_add`, `successful_sub`, and `successful_mul` laws can also
be applied directly to an existing execution equation. For example:

```lean
import Macaulean.Verification.PolynomialArithmetic
open Macaulean.M2 Macaulean.M2.Verification

example (p q out : Views.Polynomial r)
    (h : evalBinOp .mul p.value q.value = .ok out.value)
    (ctx : PolynomialArithmetic.Context) :
    PolynomialArithmetic.denote ctx out =
      PolynomialArithmetic.denote ctx p * PolynomialArithmetic.denote ctx q :=
  PolynomialArithmetic.successful_mul p q out h ctx
```

Two consequences correspond to the arithmetic updates in `m2gbReduce`:

- `move_balance`: subtracting a term from pending and adding it to the remainder
  preserves their total denotation.
- `cancel_balance`: subtracting a computed coefficient times a reducer changes
  that total by precisely the denotation of the chosen multiple.

The hypotheses are equations for the actual operator evaluator, not assumed
algebraic laws for its implementation. Neither theorem assumes that the selected
term is leading or that a particular control-flow branch is taken.

## Validation

Run `lake build MacauleanTest.PolynomialArithmetic`. The test module is also
imported by the ordinary `lake test` driver. It includes kernel-checked execution
with noncanonical rational inputs, cancellation, zero-variable rings, the two
reduction updates, malformed dimensions, and distinct rings with identical
printed names. An arbitrary-polynomial runtime theorem checks that the right
operand sees a write made by the left operand. A parsed-source example combines
execution of `(x+1)*(x-1)` with its mathematical identity at every assignment.

The test audits transitive axiom dependencies of all public arithmetic/runtime
theorems and the source/effect examples. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed; `sorryAx` and native-evaluation axioms are rejected.

## Boundaries and next mathematical steps

The original milestone supplies denotation theorems over rational assignments.
The [coefficientwise follow-up](m2-coefficient-contracts.md) now connects the same
arithmetic to the existing Stage 1 coefficient and finite-convolution views.
Neither `RuntimeReduction.RepresentationStatement` nor
`RuntimeReduction.IrreducibleStatement` is discharged by this milestone.
No parser-correctness, full reduction, termination, or full Buchberger theorem is
claimed. There are no changes to algorithm execution, approval tokens, proof
acceptance, or the existing contract definitions.

The next focused increments are:

1. Prove dimension and representation preservation for the executed
   `m2gbSubtractRow` helper, including its lexical bindings and recursive calls.
2. Establish the `m2gbReduce` representation invariant by induction on evaluation
   fuel, composing the arithmetic and row lemmas through the actual function.
3. Prove leading-term selection and irreducibility preservation separately.
4. Connect the completed representation theorem to an ideal-membership theorem
   usable through Macaulean's existing mathematical interface.

This work starts from PR #39, commit
`8a7da3a026fbaa5a37482ef229d5664d488879fb`, and therefore depends on its parent
stack. A future stacked PR should initially target
`feature/m2-proof-stage2-20260927`, then be retargeted after that stack merges.
