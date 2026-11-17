# MRDI polynomial expressions

`Macaulean.Polynomial.MRDI` provides `MrdiType (Polynomial.Expr R n)` whenever
`R` has a `MrdiType` instance. Encoding preserves the expression tree: operand
order, empty sums/products, explicit zero terms, and powers are retained without
normalization or expansion.

The MRDI type descriptor is:

```json
{"name":"Macaulean.Polynomial.Expr","params":{"coefficient":"<R descriptor>","variables":"<n>"}}
```

`coefficient` contains the actual JSON encoding of `MrdiType.mrdiType R`, which
can itself be parameterized. `variables` is a decimal natural-number string.
`fromMrdi?` checks the entire descriptor before decoding data, so incompatible
coefficient types and variable counts are rejected even for empty expressions.

The `data` field uses the following tagged arrays:

| Constructor | JSON data |
| --- | --- |
| `sum terms` | `["sum", [encoded terms...]]` |
| `product factors` | `["product", [encoded factors...]]` |
| `pow p k` | `["pow", encoded p, "k"]` |
| `term t` | `["term", [encoded coefficient, ["e₀", ..., "eₙ₋₁"]]]` |

Powers and monomial exponents are natural-number strings, including zero. The
coefficient is encoded and decoded through `R`'s existing MRDI instance, in the
same state/reference monads as the containing expression. Every monomial must
have exactly `n` exponents. Unknown tags, incorrect arities, non-array operands,
invalid coefficients, negative/non-integral exponents, and invalid dimensions
produce decoding errors, including when nested inside otherwise valid nodes.

The encoder uses structural recursion. The decoder is total and uses a decreasing
nesting budget derived from the compact JSON character count plus one. Each
nested expression requires JSON syntax characters, so this supplies a bound for
the input rather than imposing a fixed supported depth. Computing that bound
requires one compact rendering of the input JSON.

This is a new Macaulean expression representation; the previous instance was
unimplemented. The existing sparse `Polynomial R n` wire representation is
unchanged. This does not claim support for these expression tags in external
Macaulay2/MRDI packages or resolve their separate compatibility work.

Validation: `lake build MacauleanTest.PolynomialExprMRDI` exercises all constructors,
nested and empty expressions, large powers, a 200-level expression, rational
coefficients with zero variables, full JSON document round trips, metadata
mismatches, a pinned wire-format example, and malformed inputs. Dependency audits
reject `sorryAx` and other nonstandard axioms in the codec. Run `lake test` and
`lake build` for repository integration checks.
