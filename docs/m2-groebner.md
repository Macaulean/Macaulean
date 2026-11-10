# Buchberger in the M2 DSL

```lean
import Macaulean.Interpreter.DSL
open M2

R = QQ[x,y];
I = ideal(x^2-y,x*y-1);
G = gb I;

gens G
-- matrix{{y^2 - x, x*y - 1, x^2 - y}} : Matrix

(x^3-1)%G
-- 0 : QQ[x, y]

gens I * getChangeMatrix G == gens G
-- true : Boolean
```

`Macaulean/Interpreter/Buchberger.m2` is the algorithm. Leading-term cancellation,
S-polynomials, critical-pair processing, minimal-basis selection, interreduction,
monic normalization, ordering and provenance propagation are all written in M2.
There is no `rawGB` primitive, native M2 process, `IO.Ref`, or separate hidden
Lean implementation of Buchberger in production execution.

## Supported interface

The initial target is a finite list of generators in one polynomial ring over
QQ with the parent's fixed global grevlex order. `gb` accepts an ideal, a generator
row matrix, a list or sequence of polynomials, or a single polynomial. Polynomial
inputs determine the ring; scalar entries are promoted to that ring. At least
one ring-bearing input is necessary. Construct the zero ideal explicitly with
`ideal(promote(0,R))`, rather than the ring-ambiguous `ideal()`.

`gb` returns a `GroebnerBasis` data object. Its output generators are nonzero,
monic, interreduced and sorted by increasing leading monomial. Zero input
generators and repetitions remain represented in the provenance dimensions even
though they are not retained as output generators. The zero ideal returns no
output generators; a unit ideal returns the monic constant one. Zero-variable
polynomial rings are supported too.

`gens G`, `entries gens G`, `numgens G`, `ring G` and `getChangeMatrix G` inspect
the result. `ideal G` constructs the ideal of its computed generators. Functions
remain first class: they can be passed, returned, composed and stored in lists.
`normalForm` and `sPolynomial` are explicit library helpers; their names are not
a promise to reproduce every overload of an external M2 package.

`normalForm(f,G)` computes ordered division by G's generators. G may be a basis,
ideal, generator row, polynomial, list or sequence. Zero divisors in the supplied
list are skipped. With an empty list, the polynomial is unchanged. The ring must
be determined by the polynomial f or a ring-bearing G; dimension and ring checks
apply even to empty and all-zero lists. An ideal or arbitrary list is **not**
automatically replaced by its Groebner basis. Its remainder can depend on generator
order. To obtain canonical ideal normal forms, pass `gb I`.

`f % G` with a `GroebnerBasis` right operand calls the same source-language
`normalForm`; it does not use a native reduction engine. The inherited polynomial
`//` and `%` overloads with a polynomial right operand still cover single-term
divisors only. `sPolynomial(f,g)` requires two nonzero polynomials of the same ring.

## Provenance and matrix dimensions

A represented polynomial is `{p,row}` satisfying

```
p = row#0 * input#0 + ... + row#(n-1) * input#(n-1).
```

Every source-language reduction and S-pair updates both p and row. Monic
normalization scales both. The result container validates dimensions, ring
identity, normalization, nonzero monicity and this exact identity before publishing
a basis. Coefficient rows are stored per output generator.

For n original input generators and m final basis generators, `getChangeMatrix G`
has n rows and m columns. Thus `gens I * getChangeMatrix G == gens G`. The limited
matrix implementation retains dimensions when m is zero, validates products and
allows `entries`, `numRows` and `numColumns`. It is not a general module/matrix API.
No particular native M2 change matrix is required: provenance representations are
not unique, so the polynomial identity is the test, not entrywise agreement with
one engine's chosen representation.

`m2MakeBasis` is a checked **data** constructor. Its provenance check establishes
basis-to-input containment, not the reverse containment or Buchberger's criterion.
Calling that constructor manually does not manufacture a Lean theorem that an
arbitrary list is a Groebner basis. The `GroebnerBasis` runtime class is not a
proof-carrying type. Formal algebraic certification remains a separate stage.

## One parser and one evaluator

Lake tracks `Buchberger.m2` as an input dependency. `SourceFile` includes its text
as a literal string during module elaboration; `LibraryCompiler` uses the existing
M2 parser and lexical resolver to generate literal Lean `Code` data. The module
checks exact agreement between that data and compilation of the tracked source.
This elaboration check is not a universal parser-correctness theorem or an axiom.

The runtime calls a library definition by allocating an ordinary local frame and
evaluating its body with the same structurally fuel-bounded `Runtime.eval` as user
functions. No source parsing or file I/O occurs during a gb call. Library globals
are protected from reassignment and ring-variable publication. Callers' same-named
lexical locals do not alter the algorithm. Source can be edited and rebuilt; both
the library dependency and its tests must then be rechecked.

## Testing and proof boundary

The test-side checker has separately written polynomial normalization, arithmetic,
grevlex comparison, monomial divisibility, S-polynomials and reduction. It does not
call the production polynomial arithmetic or provenance checker. On each system it
checks exact provenance, both ideal containments, every final S-pair, monicity,
leading-monomial minimality and reduced tails. Deliberately corrupted outputs test
that the checker rejects missing generators, incomplete pairs, wrong provenance,
wrong dimensions, noncanonical terms, zeros, nonmonic outputs and reducible tails.
Test-oracle fuel exhaustion is an error, never success.

Native M2 supplies a second oracle. Portable exact coefficient/exponent lists are
compared, not polynomial-printer strings or foreign ring handles. Native QQ bases
may clear denominators; comparisons divide each native output by its leading
coefficient and disregard generator order, then compare all coefficients and
exponents exactly. Remainder comparisons need no such rescaling.

The suite also checks kernel-evaluated examples and actual theorem registration
for a complete basis object and a change-matrix identity. The resulting theorems
say that the M2 source evaluates to that exact value. They are not substitutes for
a universal algebraic-correctness or termination theorem. `Groebner.lean` proves
execution/dispatch and rollback contracts without adding axioms or proof holes.

The annotated worksheet covers ordinary Lean interleaving, nontrivial pairs,
reduction order, zero and unit ideals, repeated inputs, first-class calls,
provenance, exact errors and recovery. Separate tests cover saved snapshots,
caller-scope isolation, import isolation and evaluation exhaustion. All inherited
arithmetic, branching, collections, functions and polynomial tests remain enabled.

## Resource and scope boundaries

The source implements ordinary all-pairs Buchberger, not F4/F5 or a competitive
native engine. The inherited evaluator depth budget defaults to 4096; it can be
changed with `set_option m2.maxDepth ...` or explicit runtime APIs. Exhaustion
returns an error, not a partial basis. The heap remains persistent and append-only,
so substantial computations can consume considerable time and memory. No performance
claim for large systems is made.

Per-input errors roll back global writes, captured-cell writes, new rings and
allocations; prior inputs remain intact. A basis retains its original ring identity
when later inputs reuse the same printed variable names. Importing a worksheet
imports definitions, not computed rings, cells, results or its active syntax scope.

Other coefficient rings, other monomial orders, module Groebner bases, optional
native `gb` parameters, partial computations, mutable matrix objects, fractions
and full native method dispatch remain outside this restricted implementation.
