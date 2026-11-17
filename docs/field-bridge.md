# Mathematical exports over QQ and prime fields

Import `Macaulean.Verification.MathematicalExport` to write M2 worksheets and
export their values as ring-indexed mathematical objects:

```lean
import Macaulean.Verification.MathematicalExport
open M2

K = GF(5);
R = K[x,y];
I = ideal(x^2-y,x*y-1);
f = x^3-1;
G = gb I;

#m2_export "K" as K_math
#m2_export "R" as R_math
#m2_export "I" as I_math
#m2_export "f" as f_math

example : Lean.Grind.Field K_math.Carrier := inferInstance
example : K_math.characteristic = 5 := rfl

-- This is a mathematical proposition about the worksheet's actual objects:
#check I_math.Member f_math

-- Execution currently computes this remainder. A computation message alone is
-- not a theorem that G is a Groebner basis.
f % G
```

Replace `GF(5)` with `QQ` to use rational coefficients. `GF(p)` accepts a prime
integer characteristic, including 2. Use an assigned coefficient field as above,
or parenthesize a computed field: `(GF(5))[x,y]`. The existing worksheet parser's
unparenthesized application/bracket precedence is not a complete model of native
M2's array syntax.

## What an export means

`#m2_export "binding" as name` supports coefficient fields, polynomial rings,
polynomials, and ideals. Each export creates:

* `name`: the mathematical object or presentation;
* `name.source`: its exact immutable runtime snapshot;
* `name.source_eq`: a kernel-checked theorem that decoding that snapshot returns
  the exported object.

Later worksheet assignment does not change these declarations. Imported Lean
exports remain usable independently of the original worksheet session.

The shared mathematical types live in `Macaulean.Algebra`. A `PolynomialRing`
retains the coefficient field, ring identity, and ordered variable names.
`RingPolynomial ring` contains a dimension-checked sparse polynomial.
`IdealPresentation ring` contains the generators and exposes `meaning`, the
least ideal containing them, and `Member`, its membership predicate.

Polynomial equivalence is equality of every coefficient, independent of sparse
list ordering, duplicate terms, and zero terms. It is not equality of polynomial
functions. For example, x^5-x is nonzero as a formal polynomial over F_5.
The polynomial arithmetic and basis interface currently use fixed grevlex order.

The project uses its own polynomial representation and Lean's core algebra
classes; it does not currently depend on Mathlib. Ideal predicates are closed
under coefficientwise equivalence, addition, and multiplication by arbitrary
polynomials. The generated ideal has the proved least-ideal property.

## Proofs and reverse conversion

`MacauleanTest/MathematicalExport.lean` contains full proofs of
x^3-1 in (x^2-y, x*y-1) over both QQ and F_5, directly using exported worksheet
objects. They use the explicit identity x*(x^2-y)+(x*y-1)=x^3-1.

`MathematicalViews.polynomialValue`, `idealValue`, and `ringValue` convert the
mathematical presentations back to runtime values. The corresponding
`polynomial_roundtrip`, `ideal_roundtrip`, and `ring_roundtrip` theorems prove
that decoding returns the original presentation. These are explicit finite data
conversions, not a way to execute an arbitrary abstract Lean ideal in M2.

## Finite-field execution and current boundaries

Finite-field arithmetic uses canonical modular residues and the same generic
polynomial arithmetic that underlies QQ execution. The M2-language reduction and
Buchberger programs also run over these fields. Tests compare exact basis and
remainder coefficients with native M2 over F_2, F_3, F_5, and F_7, and check
change-matrix identities, nonmonic input, zero ideals, and unit ideals.

Field construction checks the inverse law over every residue and constructs a
standard `Lean.Grind.Field` instance from that evidence. This initial exhaustive
checker is suitable for small characteristics; it is not an efficient primality
algorithm. Composite moduli, zero, and one are rejected. Extension fields F_(p^k)
are not implemented in this first acceptance scope.

Rational promotion into a finite field is partial: its denominator must remain
nonzero modulo p. Thus `(1/2)*x` works in characteristic 5, while `(1/5)*x` fails.
Mixed ring identities and mixed finite fields are rejected. Ideal equality is
not implemented as a comparison of generator lists.

Gröbner certification remains under construction. A runtime `GroebnerBasis`
container and the native comparisons do not establish a general Lean theorem
that its leading terms generate the ideal's leading-term ideal. The final bridge
still needs its certificate soundness theorem and worksheet proof commands.
