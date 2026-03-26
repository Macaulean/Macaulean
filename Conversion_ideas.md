# Conversions between Lean and Macaulay2

## Implemented

|Lean gives|Macaulay2 returns|Notes|
|-|-|-|
|Integer|Factorisation|Certified: Lean checks product of factors equals target|
|(Ideal, polynomial)|Quotient-remainder certificate|Over $\mathbb{Z}[x_1, \ldots, x_n]$; zero remainder derives ideal membership|
|Polynomial|Sum-of-squares certificate|Returns scale $s$ and summands $(w_i, q_i)$ such that $s \cdot f = \sum w_i q_i^2$; works over any ordered field with $\mathbb{Q}$-algebra structure|

## Planned

|Lean gives|Macaulay2 returns|Notes|
|-|-|-|
|Polynomial|Factorisation|M2 can compute this; Lean-side certificate format for irreducibility is the open design question|
|Ideal|Gröbner basis|`TaskKind.groebnerBasis` exists in the enum but is not yet implemented; currently GB computation is implicit inside quotient-remainder|

## Architecture

The full CAS backend architecture and implementation status are documented in [CAS_ARCHITECTURE.md](CAS_ARCHITECTURE.md).
