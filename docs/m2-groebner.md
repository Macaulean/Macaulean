# QQ polynomials and Buchberger in the M2 language

```lean
import Macaulean.Interpreter.DSL
open M2

R = QQ[x,y];
I = ideal(x^2-y,x*y-1);
G = gb I;

gens G
-- matrix {{y^2 - x, x*y - 1, x^2 - y}} : Matrix

(x^3-1)%G
-- 0 : QQ[x, y]

(x+y)%G
-- x + y : QQ[x, y]

gens I * getChangeMatrix G == gens G
-- true : Boolean
```

Every input is a normal M2 command in a Lean file. Outputs use the existing
InfoView message stream; semicolons suppress display. The annotated executable
worksheet is `MacauleanTest/InterpreterGroebnerDSL.lean`.

## What runs where

`Macaulean/Interpreter/Buchberger.m2` is the implementation of polynomial
reduction, S-polynomials, critical-pair processing, minimal-basis cleanup,
interreduction, monic normalization, and output ordering. These are M2 function
bodies executed by the same pure lexical runtime as user functions. There is no
`rawGB` primitive and no foreign engine call in the DSL execution path.

The source library is parsed and resolved at build time into ordinary Lean code
data. The resolved code is checked against its source definition. Lake tracks
the `.m2` source as an input-file dependency, so changing it invalidates the
library build. The source remains the implementation, not a comment accompanying
a different Lean algorithm.

The first-order Lean backend provides rational polynomial arithmetic and
observations: addition, subtraction, multiplication, powers, rational scaling,
leading terms, monomial divisibility, monomial least common multiples, and exact
monomial quotients. It reuses `Macaulean.Polynomial Rat n` and normalization.
The runtime arithmetic path is structurally recursive and kernel-executable;
it deliberately avoids the older backend routines whose definitions cannot
reduce through `Classical.choice` in the kernel.

## Supported interface

The coefficient field is QQ, the variables commute, and the fixed global
monomial order is graded reverse lexicographic order. `QQ[]` is supported.
Distinct ring constructions have distinct runtime identities even when their
printed variable names agree. Polynomials from different rings are rejected
rather than silently mixed.

The frontend supports `QQ[x,y]`, `QQ[local x,local y]`, variable promotion such
as `0_R`, `R_0`, scalar and polynomial arithmetic, `ideal`, `gens`/`generators`,
`ring`, `numgens`, `entries`, `flatten`, `leadCoefficient`, `leadMonomial`,
`leadTerm`, `exponents`, `listForm`, `terms`, `promote`, and `size` for their
implemented cases. Numerator and denominator operations are available for
scalars. A small polynomial matrix interface supports generator matrices,
entry access, multiplication, subtraction, and equality; this is not a general
module or matrix-algebra implementation.

`gb` returns a basis object containing the original ideal, the final generators,
and their expressions in the original generators. `getChangeMatrix` exposes
those expressions as a matrix. The result factory verifies those identities
before publishing the object. `%` on a polynomial and a basis evaluates the
source-language normal-form routine.

Precedence is M2 precedence, not Lean notation precedence. In particular,
`numgens (QQ[x,y])` requires parentheses: `numgens QQ[x,y]` first applies
`numgens` to QQ. The native convention `leadMonomial(0_R) = 0_R` is preserved.
Zero-polynomial negative powers also retain the native zero result; scalar
rational division by zero is still an error.

## Algorithm and provenance

The implementation starts with monic nonzero input generators and unit
representation rows. Each reduction and S-polynomial operation updates both
the polynomial and its representation in the original inputs. A pending pair
queue is processed until empty; each new nonzero remainder adds its pairs with
the current basis. Cleanup removes redundant leading monomials, interreduces,
normalizes coefficients, and orders the result deterministically.

There are no advanced pair criteria, F4/F5 algorithms, modular arithmetic,
parallel execution, or asymptotically optimized polynomial data structures.
This implementation is intended as an inspectable source-language algorithm
and a foundation for verification, not a performance replacement for native M2.

## Verification layers

Tests use explicit expected sparse coefficient/exponent data, rather than
comparing polynomial display strings. Native M2 comparisons observe monic
reduced bases and compare multisets, avoiding accidental dependence on output
order or nonmonic scaling.

A separate Lean test checker verifies representation identities, reduction of
the original generators, vanishing of every S-polynomial, and monic reducedness.
It is independent of the M2 pair loop and reduction code. Successful test cases
must finish; a resource limit or an error is not an accepted partial basis.

Kernel tests execute polynomial operations and small complete source programs.
An actual `addRunTheorem` regression constructs a kernel-checked theorem that a
GB program evaluates to its expected typed result. This proves execution of
that program. It is **not** a general theorem proving Buchberger's criterion,
termination, or the mathematical correctness of every result. The soundness of
the independent algebraic checker and a general connection to polynomial ideal
semantics remain further proof work.

## Resources and unsupported fragments

Recursion is bounded by the existing explicit depth budget, configurable using
`set_option m2.maxDepth ...`. Exhaustion is an error, not a truncated basis.
The current runtime uses an append-only lexical heap without garbage collection.
The inherited transaction rule applies per worksheet input: failure rolls back
that input's assignments, allocations, and ring-variable writes, while earlier
successful inputs and their snapshots remain unchanged. This differs from
native M2's behavior after some side-effecting errors.

Polynomial rings over ZZ or finite fields, quotient rings, ring towers,
fraction fields, user-selected monomial orders, indexed variable families,
modules, syzygies, and native `gb` options/caching/computation objects are not
implemented. Purely scalar `ideal()`/`ideal 0` do not infer a polynomial ring;
use `ideal(0_R)` for the zero ideal. General symbolic-language behavior and
native method installation are also outside this fragment.
