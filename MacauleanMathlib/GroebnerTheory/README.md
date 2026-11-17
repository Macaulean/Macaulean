# Gröbner theory provenance

These proof modules are adapted from [WuProver/groebner_proj](https://github.com/WuProver/groebner_proj),
commit `5ae0d42ebd6d9abd129c19c1e3720418eb590246`, by Junyu Guo and Hao Shen.
They are distributed under the accompanying Apache 2.0 LICENSE; source copyright
headers are retained. Only the dependency closure of `Groebner.Groebner` is included.

Local changes adapt the sources from Lean/Mathlib 4.34.1 to the repository's
4.33.1 toolchain: older coefficient APIs and theorem names, zero-based TFAE indices,
explicit well-foundedness packaging, and removal of unsupported deprecated-attribute
syntax. Imports use the local module path. The mathematical statements are unchanged.

The principal theorem is
`MonomialOrder.IsGroebnerBasis.iff_isRemainder_sPolynomial_zero`.
Its conclusion uses equality of leading-term ideals. Remainder certificates include
bounds on the degrees of representation summands; ideal membership alone does not
satisfy this criterion.

This dependency is used by the mathematical certification layer. The interpreter
and the executable polynomial certificate arithmetic retain their existing imports.
