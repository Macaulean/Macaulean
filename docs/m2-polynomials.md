# QQ polynomials in the M2 worksheet

```lean
import Macaulean.Interpreter.DSL
open M2

R = QQ[x,y];
p = (x+y)^2;
listForm p
I = ideal(x^2-y,x*y-1);
entries gens I
ring p === R
```

The polynomial layer supports exact rational coefficients, default grevlex,
scalar promotion, arithmetic, leading terms/coefficients/monomials, `exponents`,
`listForm`, `terms`, `size`, `coefficient`, ideals and generator-row inspection.
`//` and `%` in this layer handle single-term polynomial divisors only.
General polynomial reduction and Buchberger belong to the next stacked PR.
`/` by a polynomial requires a fraction field and is rejected, even when the
quotient would simplify to a polynomial. `leadMonomial(0_R)` is an error in the
native version tested; `leadTerm(0_R)` and `leadCoefficient(0_R)` are zero.
Use `promote(0,R)` where subscripted promotion syntax is unavailable.

## Identity and bracket binding

`===` and `=!=` are strict equality and inequality. They do not promote ZZ to QQ
or a polynomial ring. In particular use `ring p === R`, not `ring p == R`:
the tested native M2 has no ring-valued `==` method. Polynomial `==` continues
to allow scalar promotion. Strict comparisons of immutable lists and algebra
data compare their typed contents; closures compare session handles.

Bracket identifiers are looked up in their lexical scope before any generator
is published. An unbound global supplies its name. An existing indeterminate
supplies its original generator name, not the alias used to reach it:

```m2
R=QQ[x]; old=x; S=QQ[old];
ring old === R -- true
ring x === S   -- true
```

A null local contributes no generators. A single integer-valued identifier
requests that many anonymous generators, with nonpositive counts producing none;
`gens R` gives access to their `p_0`, `p_1`, ... indeterminates. The integer-valued
identifier is not overwritten. Indexed-name syntax itself is outside this parser.
Creating anonymous indexed generators invalidates an old global `p` binding;
reading the resulting unbound global symbol is outside the scalar interpreter's
supported read semantics. Do not mix an integer count with other bracket values.
Repeated names, indexed-generator rebinding and quoted-local symbol binding are
explicit extension boundaries, not silently approximated forms of `QQ[x,y]`.
Non-generator polynomial expressions in brackets are rejected.

The bracket constructor allocates fresh ring identities in immutable session
state. Saved polynomial values retain their original rings. Cross-ring arithmetic
is rejected. Failed worksheet commands roll back generator publication and ring
allocation. Imports do not carry worksheet state to another Lean module.

## Monomial helpers

`m2MonomialDivides`, `m2MonomialQuotient`, `m2MonomialLCM`,
`m2MonomialCompare`, and `m2Monomial(R,exponents)` are explicitly named extension
helpers, not complete replacements for native overloaded methods. The first four
expect nonzero single-term polynomials. Divisibility ignores a nonzero scalar;
quotient includes the scalar quotient; LCM is monic; comparison ignores the scalar
and uses grevlex. Dimensions, signs, ring identity and divisibility are checked.

## Verification boundary

Raw coefficient/exponent lists are checked before decoding to Macaulean's existing
dependent polynomial representation. `KernelPolynomial` supplies structural
sorting/normalization and arithmetic because the backend's current sorting path
does not reduce in the Lean kernel. Representation bridge theorems name this
kernel evaluator explicitly; they do not assert a proved equivalence to every
backend optimization.

Each corpus value and specified error receives a separate kernel-checked source
execution theorem. Rejection-boundary theorems check failure without forcing
pretty-printed parser diagnostics through kernel reduction. One large aggregate
`decide` exhausted worker memory; separate theorems retain the same input coverage.
The native differential suite uses a fresh M2 process per query and checks typed
coefficient/exponent data against independently written expected values. Process
failure and malformed transport are errors, not successful rejection tests.
There are additional arithmetic and monomial grids, worksheet formatting/source
location checks, snapshot/rollback tests and import-isolation checks.

These are execution and representation guarantees, not a universal theorem of
Buchberger correctness. There is no native M2 call in polynomial execution.
