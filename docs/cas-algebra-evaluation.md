# `CASAlgebra`: explicit coefficients, evaluated

An evaluation, not a design document.  The question is whether the certificate
machinery should grow a second level -- an `Algebra R A` shape in which the
*coefficients* are themselves polynomial expressions in a base ring -- and what
that would cost.  The answer, up front, is in the last section; the reasoning is
in the four before it.

Two trees are quoted throughout:

* **this branch**, `poly-repr-reflect`, at `Macaulean/…`;
* **the old branch**, `gmp-free-certificates` in `/Users/worker/Macaulean`,
  which had a two-level `Algebra R A` design and is quoted as
  `[gmp-free] Macaulean/…`.

Everything measured here was measured on this machine (Lean v4.33.1, Apple
silicon); the micro-benchmark is described in §5 and its numbers are reproducible
from the description.


## 1. Where `Int` is wired in today

The kernel carrier is `Macaulean.Polynomial Int nv` and the coefficient map is
`CASRing.ofInt : Int → R` (`Macaulean/CASRing.lean:131`), pinned down by
`ofInt_isCoeffHom : Polynomial.IsCoeffHom ofInt` (`:134`).  Rational cofactors
never reach the kernel: they are cleared by scaling the whole certificate by a
common denominator `d` and cancelling it afterwards through `CASRingRat`
(`Macaulean/CASRing.lean:180-219`, `Macaulean/PolyCert.lean:141-218`).

What is worth knowing is how *little* of the stack is actually `Int`-specific.

**Already generic in the coefficient type `C`:**

| Where | What |
| --- | --- |
| `Macaulean/Polynomial/Basic.lean:60` | `Polynomial (R : Type) (n : Nat)` |
| `Macaulean/Polynomial/Basic.lean:509,522,555,560` | `add`, `sub`, `mul`, `pow`, all `[Grind.CommRing R]` |
| `Macaulean/Polynomial/Hom.lean:28` | `IsCoeffHom {C A} [Grind.CommRing C] [Grind.CommRing A] (φ : C → A)` |
| `Macaulean/Polynomial/Hom.lean:48` | `denoteWith (φ : C → A) (ctx) (p : Polynomial C n) : A` |
| `Macaulean/Polynomial/Hom.lean:126-210` | every `denoteWith_*` lemma, under `[BEq C] [LawfulBEq C]` |
| `Macaulean/Grind/AlgPoly/Expr.lean:27` | `AlgExpr (C : Type)` |
| `Macaulean/Grind/AlgPoly/Expr.lean:41` | `AlgExpr.denote (φ : C → A) ctx` |

**Specialised to `Int`, and only here:**

| Where | What |
| --- | --- |
| `Macaulean/Grind/AlgPoly/Expr.lean:72-115` | the rebalancing family (`sumList`, `pairUp`, `balFuel`, `balance`, `addChain`, `rebalance`), all `AlgExpr Int` |
| `Macaulean/Grind/AlgPoly/Expr.lean:129-235` | `denoteList` and the six lemmas ending in `denote_rebalance` |
| `Macaulean/Grind/AlgPoly/PolyEval.lean:31,66` | `toPoly nv : AlgExpr Int → Option (Polynomial Int nv)`, `checkPolyEq` |
| `Macaulean/Grind/AlgPoly/PolyEval.lean:79,143` | `denote_toPoly`, `eq_of_checkPolyEq` |
| `Macaulean/Grind/AlgPoly/Reify.lean:28-53` | `intTypeE`, `intLitE`, `mkCtor`, `mkCoeff` |
| `Macaulean/Grind/AlgPoly/Tactic.lean:66-108` | `CASRingData.phi`/`hphi`/`mkOfInt` |
| `Macaulean/CASRing.lean:70,131,182` | `intDenote`, `CASRing.ofInt`, `CASRingRat.invOfInt` |

So the *polynomial* layer needs no work at all; the work is in `AlgExpr` and in
the tactic.


## 2. What the old branch actually did

### The class

`[gmp-free] Macaulean/Grind/Algebra/Defs.lean:22`:

```lean
class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    extends SMul R A where
  toFun : R → A
  map_zero, map_one, map_add, map_mul
  commutes : ∀ (r : R) (x : A), toFun r * x = x * toFun r
  smul_def : ∀ (r : R) (x : A), r • x = toFun r * x
```

with `algebraMap R A := Algebra.toFun` (`:34`), a dozen `@[grind =]` E-matching
lemmas (`:41-105`), and instances for the identity algebra, `Nat`, `Int` and a
characteristic-zero field over `Rat`
(`[gmp-free] Macaulean/Grind/Algebra/Instances.lean:26,43,55,67`).
`Extension.lean` registers a grind solver extension whose `internalize` and
`newEq` handlers are both `return ()` (`:53-58`) -- it is a placeholder, not a
solver, and its own docstring says so (`:17-31`).

### The reification

Two atom tables, not one
(`[gmp-free] Macaulean/Grind/AlgPoly/Reify.lean:127-133`):

```lean
structure State where
  coeffVars : Array Expr := #[]
  coeffVarMap : Std.HashMap Expr Nat := {}
  ambientVars : Array Expr := #[]
  ambientVarMap : Std.HashMap Expr Nat := {}
```

`isAlgebraMapApp?` (`:227`) recognises `algebraMap R A c` up to defeq;
`reifyAmbientExpr` (`:241`) sends the argument to a *second* reifier
`reifyCoeffExpr` (`:195`), which produces a `Lean.Grind.CommRing.Expr` and then
`Expr.toPoly` (`:224`).  The result is an `AlgExpr Lean.Grind.CommRing.Poly` --
grind's own `Int`-coefficient polynomial as the coefficient carrier.  The
soundness bridge is `polyCoeffIsRingHom` (`:40`), which says that
`p ↦ algebraMap R A (Poly.denote coeffCtx p)` is an `IsRingHom` (this branch's
`IsCoeffHom`).

The tactic's `Inputs` (`[gmp-free] Macaulean/Grind/AlgPoly/Tactic.lean:64-74`)
carries `R`, `A`, `algebraMapFn`, `algebraInst`, the two reified sides, and the
two variable arrays.  `findAlgebraMapFn?` (`:76`) looks for an `algebraMap`
application in the goal and falls back on the self-algebra when there is none
(`:103-113`), so single-ring identities go through the same pipeline with
numerals as coefficients.

### The coefficient class

`[gmp-free] Macaulean/Grind/AlgPoly/Basic.lean:42`:

```lean
class CoeffRing (C : Type u) extends Zero C, One C, Add C, Mul C, Neg C, BEq C where
  beq_sound : ∀ a b : C, (a == b) = true → a = b
```

with instances for `Int` and `Lean.Grind.CommRing.Poly` (`:48,52`).  Note what
it is *not*: not a `CommRing`.  Reflective evaluation needs the operations and a
sound equality test, and nothing else; the ring axioms enter only through the
hom `φ`.  That is the right shape and this branch should copy it.

### What the old branch did **not** get

Two kernel paths, and only one of them tolerated a non-constant coefficient.

* `proveModPath` (`[gmp-free] .../Tactic.lean:407` ff.) -- the GMP-free
  residue-vector certificate -- begins by re-coefficienting the reified sides
  from `Poly` back to `Int` with `toAlgIntE?` (`:207`), whose own comment says
  it answers `none` "when some coefficient is not a plain integer (e.g. it
  mentions a coefficient-ring variable coming through `algebraMap`)".  A genuine
  `ℚ(t)`-coefficient identity failed this path outright.
* `proveReifiedEq` (`:474` ff.) -- the exact-integer Kronecker path -- *did*
  keep `C = Grind.CommRing.Poly` and hand `AlgExpr.checkKEq` to
  `decide +kernel` with `coeffRingPolyInst`.  This is the only place the
  two-level design ever reached the kernel with polynomial coefficients.
* Below that, the cons-list `AlgPoly` normal form and then `simp`/`grind`
  (`:608-700`), which is the superlinear route the current branch exists to
  avoid.

So the honest summary of the old branch is: the *plumbing* for polynomial
coefficients was complete and the *fast* path was half of it.


## 3. (a) What `CASAlgebra` would need beyond `CASRing`

### The coefficient carrier

`CASRing A` fixes `ofInt : Int → A`.  `CASAlgebra C A` would fix
`ofCoeff : C → A` together with `IsCoeffHom ofCoeff`, plus enough structure on
`C` for the kernel to compute.  Three candidates:

| `C` | kernel-evaluable? | canonical normal form? | verdict |
| --- | --- | --- | --- |
| `Int` | yes | yes | today |
| `Lean.Grind.CommRing.Poly` | yes | yes (grind's `combine`/`mul` drop zeros) | what the old branch used |
| `Macaulean.Polynomial Int m` | yes | **no** -- see below | needs one extra field |
| `Rat` | no (`Nat.gcd` is an out-of-line GMP call) | yes | ruled out, and that is the reason `/ d` exists |

Nested `Polynomial (Polynomial Int m) n` is the natural choice for this
repository, because it reuses the packed-key monomial representation
(`Macaulean/Polynomial/Key.lean:35-39`) at both levels and because `denoteWith`
and `IsCoeffHom` are already stated for a general `C`.  It has one defect, and
it is measured rather than guessed.

**The zero test is not decisive.**  `checkPolyEq`
(`Macaulean/Grind/AlgPoly/PolyEval.lean:66`) compares
`removeZeros p.terms == removeZeros q.terms`.  `removeZeros`
(`Macaulean/Polynomial/Basic.lean:367`) tests `t.coefficient == 0` with the
`[Zero C] [BEq C]` it is given, and the soundness lemma
`denoteTerms_mapCoeffTerms_removeZeros` (`Macaulean/Polynomial/Hom.lean:109`)
needs `[LawfulBEq C]`.  For `C = Int` the derived structural `BEq` is a decision
procedure for "is this coefficient zero".  For `C = Polynomial Int m` it is not:
`add` and `mul` deliberately do **not** strip zero coefficients (that is the
`removeZeros`-once design recorded in `docs/poly-repr-reflect.md`), so a
coefficient can be mathematically zero and structurally `⟨[⟨0, unit⟩]⟩`, or
structurally `⟨[]⟩`, and neither equals the other.

Measured, in `Polynomial (Polynomial Int 1) 3` with `T` the inner variable:

```
(x + T) * (x − T)   vs   x^2 − T^2          checkPolyEq-style compare: FALSE
T * y + (−T) * y    vs   x − x              checkPolyEq-style compare: FALSE
```

Both are true identities.  Re-normalising the inner coefficients
(`⟨removeZeros p.terms⟩`) and replacing the outer zero test by "the coefficient's
normal form has no terms" makes both compare `true`.  So the fix is small but it
is *not* optional, and it is exactly a class field: `CoeffRing`-style
`isZero : C → Bool` with `isZero c = true → φ c = 0`, plus a `normalize : C → C`
applied after every coefficient operation.  The old branch got away with plain
structural `BEq` (`beq_sound`) only because grind's `Poly` is canonical by
construction.

### The reification

`algebraMap R A c` and `r • x` have to become nodes of
`Macaulean.AlgPoly.Reify.Node` (`Macaulean/Grind/AlgPoly/Reify.lean`, the
classifier added for the shared atom table), and the atom state has to split
into a coefficient table and an ambient table, as
`[gmp-free] .../Reify.lean:127-133` did.  Concretely:

* `Node` gains `| coeffExpr (c : Expr)` (the argument of `algebraMap`) and
  `| smul (r x : Expr)`;
* `AtomState` becomes a pair of tables, and `classify` takes the `algebraMapFn`
  the way `reifyAmbientExpr` did;
* `mkCoeff` stops taking an `Int` and takes a reified coefficient term.

Note that **without** any of this, `algebraMap R A c` is already an *atom* under
the current classifier, and so is `ξ` itself.  That is sound, and it is the
trivial alternative discussed in §5.

### The soundness lemmas to generalise

Eight, all of the form `Int → C` with `[Grind.CommRing C] [BEq C] [LawfulBEq C]`:

* `AlgExpr.denoteList`, `denote_sumList`, `denoteList_pairUp`, `denote_balFuel`,
  `denote_balance`, `denoteList_addChain`, `denote_rebalance`
  (`Macaulean/Grind/AlgPoly/Expr.lean:129-235`);
* `AlgExpr.denote_toPoly` and `AlgExpr.eq_of_checkPolyEq`
  (`Macaulean/Grind/AlgPoly/PolyEval.lean:79,143`).

None of them uses anything about `Int` beyond the `IsCoeffHom` interface -- the
proofs are already written against `hφ.map_zero`, `hφ.map_add`, `hφ.map_mul`,
`hφ.map_neg`.  The `Polynomial` layer (`Macaulean/Polynomial/Hom.lean`) needs no
change whatever; `denoteWith` over a non-`Int` `C` is what that file already
says.  One genuinely new lemma is needed: that the generalised zero test is
sound (`isZero c = true → φ c = 0`), replacing the `[LawfulBEq C]` argument of
`denoteTerms_mapCoeffTerms_removeZeros`.

`IsCoeffHom` for a *polynomial* hom -- `φ = fun p => denoteWith ofInt coeffCtx p`
composed with `algebraMap` -- is one new theorem, and the old branch has it
written out: `[gmp-free] .../Reify.lean:40-67`, about 25 lines, four rewrites
per field.


## 4. (b) Replace `CASRing`, or sit beside it?

**Beside it.**  Three reasons.

*Instance resolution.*  `CASRing R` is a one-parameter class whose parent
projection is deliberately priority 100 so a concrete ring's own
`Grind.CommRing` instance still wins (`Macaulean/CASRing.lean:138`, and the
`#synth` guards in `MacauleanTest/PolyCert.lean` that pin that down).  A
two-parameter `CASAlgebra C A` is resolved once per certificate by
`casRingData` (`Macaulean/Grind/AlgPoly/Tactic.lean:87`) with `C` unconstrained
by the goal -- i.e. with `C` a metavariable at synthesis time, which is the case
`trySynthInstance` handles worst.  Defining `CASRing R := CASAlgebra Int R`
would put that cost on every goal in the library, including the ones (all of
them, today) that have integer coefficients.

*The kernel fast path.*  Coefficient arithmetic must stay on Lean's small-`Nat`
path.  Nested polynomials do (§5 measures it: they are *faster*, not slower).
`Rat` does not, which is the whole reason for the `/ d` scaling
(`Macaulean/PolyCert.lean:48-52`).  A class that admits both would have to be
gated anyway, so the gate may as well be the instance's existence.

*What Macaulay2 needs.*  This is where the difference bites.

`QQ[t][x,y]` and `frac(QQ[t])[x,y]` are different requests.  Over the polynomial
ring the cofactors come back in `QQ[t]` and everything works as it does now.
Over the fraction field, `quotientRemainder` returns cofactors with denominators
in `t`, and the `/ d` trick generalises to a *polynomial* scale factor `d(t)`:
the kernel checks `ofCoeff d * (p − r) = Σ qᵢ' gᵢ`, and `d` is cancelled
afterwards.  Cancelling it is the problem.

`CASRingRat.mul_invOfInt` (`Macaulean/CASRing.lean:184`) asks for a right
inverse of `ofInt d`.  The analogue -- a right inverse of `ofCoeff d(t)` in
`A = ℚ[t][x,y]` -- **does not exist**: `d(t)` is not a unit there.  So the class
field cannot be an inverse; it has to be a cancellation law,

```lean
cancel_ofCoeff : ∀ c : C, ¬ isZero c → ∀ a b : A, ofCoeff c * a = ofCoeff c * b → a = b
```

which is a `NoZeroDivisors` / `IsDomain`-style hypothesis on `A` together with
injectivity of `ofCoeff` (equivalently: `ofCoeff c` is a non-zero-divisor for
every nonzero `c`).  That is the class field the fraction-field route needs, and
it is strictly weaker than `CASRingRat`.  The price is that the *divisibility*
shape has to be dropped on that route: `CASRingRat.dvd_witness`
(`Macaulean/CASRing.lean:209`) produces the witness `q'/d` for `g ∣ f`, and
cancellation cannot produce a witness -- the docstring of `CASRing.lean:43-48`
already says exactly this about the integer case.

Two smaller consequences on the wire:

* `d ≠ 0` stops being `decide`-able the way `intNeZeroProof`
  (`Macaulean/PolyCert.lean:118`) is.  For a polynomial `d(t)` it becomes a
  normal-form check (`d.terms ≠ []` after `removeZeros`) plus the hom being
  injective on nonzero coefficients -- which is the same `IsDomain`-flavoured
  hypothesis again.
* `M2BaseRing` (`Macaulean/CASRing.lean:98`) is an enum with two constructors
  and `toString` giving `"ZZ"`/`"QQ"`.  It would have to carry the coefficient
  variable names and a polynomial-vs-fraction flag, and `m2/macaulean.m2` would
  have to build a two-level ring: today `leanRings` (`m2/macaulean.m2:26`) is a
  fixed table and the ring is built as `kk[vars(0..<n)]` (`:60,88`) with `kk` a
  base field.


## 5. (c) The concrete use case, and (d) what it would cost

### The use case

`/Users/worker/explicit-unirational` pins Macaulean at `05e592e5`
(`lakefile.toml:19`) and uses the reflective checker in exactly one file,
`ExplicitUnirational/FunctionField/TowerBProducts.lean` -- `poly_def` constants
and `algebra_norm_reflect`, over `MvPolynomial (Fin 3) ℚ`, with coordinates
`X 0 = X`, `X 1 = Y`, `X 2 = z` (`.../TangentResidual.lean:49`).  The reduced
forms it works with are `gAff`, `redH2`, `redTheta`
(`.../TangentResidual.lean:65,297,519`), all in that ring.

Item (3) of `.../ResidualDegree.lean` (`:54`, size report `:61-84`, orientation
`:313-337`) wants

```
Res_Y (gAff, redTheta − ξ · redH2) ∈ ℚ[X, z, ξ]
```

-- 1055 terms, `deg_X = 18`, `deg_ξ = 3`, `deg_z = 26`, content 1 -- with `ξ`
transcendental.  Read as a statement, that is `Algebra ℚ[ξ] ℚ[ξ][X, z]`-shaped.

**It does not need `CASAlgebra`.**  `ξ` occurs polynomially, to degree 3, with
no denominators.  So `A · gAff + B · f = Res` is an ordinary polynomial identity
in the four variables `X`, `Y`, `z`, `ξ`, and the reflective checker takes it as
such -- in `MvPolynomial (Fin 4) ℚ`, or, with no type change at all, with `ξ` a
plain local of `MvPolynomial (Fin 3) ℚ`, which the atom rule accepts as a fourth
ring variable (any maximal non-arithmetic subterm is a variable; that is what
`Reify.classify` says, and since this branch's Macaulay2 half shares that
classifier, `m2cert` will serialise it too).  The kernel then works over
`Polynomial Int 4` exactly as it works over `Polynomial Int 3` today; the
monomial key base drops from `2^20` to `2^15` (`Macaulean/Polynomial/Key.lean:35`),
which still holds `deg_z = 26` and `deg_X = 18` comfortably.

What blocks item (3) is not the coefficient ring.  It is that the Bézout
cofactors are 794-921 terms at stage 0 and the remainder is 579
(`.../ResidualDegree.lean:76-84`), which `ring` cannot do -- and that is a size
problem the reflective certificate exists for.  The next step there is `m2cert`
on the four-variable identity, not a coefficient tower.

`CASAlgebra` becomes *necessary* only one layer up, where the coefficient object
is genuinely a fraction field in the type: the `RatFunc ℚ` / `AdjoinRoot`
material of `.../ResidualDegree.lean:14-18,141,187,250`.  There `ξ` is not a
polynomial variable and denominators in `z` are unavoidable, and no amount of
"add another ambient variable" reaches it.

### The measurement

Does the extra polynomial layer cost the kernel anything?  Measured, not
guessed.  Two files, identical mathematics, differing only in where the fourth
variable `t` lives:

* **flat**: `Polynomial Int 4`, variables `x, y, z, t`;
* **nested**: `Polynomial (Polynomial Int 1) 3`, ambient variables `x, y, z`,
  coefficient variable `t`.

Each checks a product identity by `decide +kernel` on
`removeZeros lhs.terms == removeZeros rhs.terms`, where `lhs` and `rhs` compute
the same product by different associations.  Wall clock for
`lake env lean <file>`, less a 0.49 s baseline for the imports alone; each figure
stable to ±0.02 s over repeats.

| identity | flat monomials | flat | nested (outer × inner) | nested | ratio |
| --- | ---: | ---: | --- | ---: | ---: |
| `p^6` vs `p^3·p^3`, `p = 1+x+y+z+t` | 210 | 0.35 s | 84 × ≤7 | 0.28 s | 0.80 |
| `p^8` vs `p^4·p^4` | 495 | 1.62 s | 165 × ≤9 | 1.00 s | 0.62 |
| `p^10` vs `p^5·p^5` | 1001 | 6.31 s | 286 × ≤11 | 3.29 s | 0.52 |
| `q^10·r^3` vs `(q^5 r)(q^5 r^2)`, `q = 1+x+y+z`, `r = 1+t` | 1144 | 8.15 s | 286 × ≤4 | 2.33 s | **0.29** |

The extra layer does not cost; it *pays*.  The reason is structural: the
dominant cost in `Polynomial.mul` is `mergeTerms` over the outer term list, and
moving one variable into the coefficient shrinks that list by the factor the
variable contributed while replacing each coefficient `Int` operation by a merge
of two very short lists.  The last row is the shape that matters here -- one
low-degree variable (`deg_ξ = 3`) against several high-degree ones -- and it is
the biggest win.

Caveats, stated plainly: the benchmark supplies `Grind.CommRing (Polynomial Int m)`
with its `Prop` fields `sorry`ed, which is sound as a measurement (`decide
+kernel` on a `Bool` never looks at them) and useless as mathematics; the inputs
have no cancellation, so the normal-form defect of §3 does not bite; and the
inner polynomials are dense and short, which is the favourable regime.  A real
implementation pays for `normalize` on every coefficient operation, which the
benchmark does not.

### The cost

Files touched, with what changes:

| File | Change |
| --- | --- |
| `Macaulean/Grind/AlgPoly/Expr.lean` | rebalancing family and 6 lemmas, `Int → C` |
| `Macaulean/Grind/AlgPoly/PolyEval.lean` | `toPoly`, `checkPolyEq`, 2 lemmas, `Int → C` |
| `Macaulean/Polynomial/Basic.lean` | `removeZeros`'s zero test through a class field |
| `Macaulean/Polynomial/Hom.lean` | one new lemma for that test (the rest is already generic) |
| `Macaulean/CASRing.lean` | `CoeffRing`-style class, `CASAlgebra C A`, the cancellation field, `M2BaseRing` grows |
| `Macaulean/Grind/AlgPoly/Reify.lean` | second atom table, `algebraMap`/`smul` nodes, coefficient reifier (~+120 lines, and the old branch's `:195-271` is the template) |
| `Macaulean/Grind/AlgPoly/Tactic.lean` | `CASRingData` → the old `Inputs` shape, two contexts, the composed hom |
| `Macaulean/PolyCert.lean` | `/ d(t)`, the non-`decide` nonzero check, cancellation instead of inverse |
| `Macaulean/M2Cert.lean`, `Macaulean/IdealMembership.lean`, `m2/macaulean.m2` | two-level base ring on the wire |

Nine files, eight lemmas to generalise (all mechanical), one new soundness lemma
for the zero test, one new `IsCoeffHom` witness (25 lines, already written on the
old branch), and one genuinely new piece of design: the cancellation field and
its `IsDomain`-style side condition.  Expected kernel slowdown: **none** -- the
measurement says the layer is a speed-up in the regime that matters, and the
`normalize`-per-operation the benchmark omits is `O(terms)` per coefficient
operation on lists that are short by construction.

### The trivial alternative

Treat the coefficient variable as one more ambient variable.  This costs
nothing, is already implemented, and is *correct for every identity in which the
coefficient variable occurs polynomially*.  It is enough exactly when:

* the goal is an identity (not a divisibility with a non-integral witness), and
* the coefficient variable appears with no denominators, and
* the extra variable keeps the packed monomial key under `2^62` --
  `Macaulean/Polynomial/Key.lean:35` gives `bits n = max 8 (62 / n)`, so the
  budget per variable is 15 bits at 4 variables, 12 at 5, 10 at 6, and
  `algebra_norm_reflect` already warns when it is exceeded
  (`Macaulean/Grind/AlgPoly/Tactic.lean:229-233`).

It is *not* enough when:

* the coefficient object is a fraction field in the type (`RatFunc`,
  `FractionRing`), so that "add a variable" changes the statement;
* Macaulay2 has to divide over `frac(QQ[t])` and returns denominators in `t`;
* the statement is about a module or an algebra structure per se (`smul`
  appearing in the goal), rather than about an element identity;
* the added variable pushes the key past the small-`Nat` range, at which point
  the two-level packing (which gives each level its own budget) is the only way
  to stay on the kernel's fast path.


## 6. Recommendation

**Do not build `CASAlgebra` now.  Build the one piece of it that is cheap and
independently useful, and keep the trivial alternative as the default.**

1. **Default to the extra ambient variable.**  For `explicit-unirational`'s item
   (3) it is exactly right, it needs no new code, and the blocker there is
   certificate size, which `m2cert`/`poly_cert` already address.  Say so in
   `docs/poly-repr-reflect.md`.
2. **Do generalise `AlgExpr` and `PolyEval` from `Int` to a `C` with a
   `CoeffRing`-style class.**  Eight mechanical lemma generalisations, no design
   risk, and it is the prerequisite for everything else.  Do it when something
   needs it, not before.
3. **Fix the zero test as part of that.**  `removeZeros`' `== 0` has to become a
   class field with a soundness lemma; without it the nested carrier silently
   fails on any identity with cancellation, which is most of them.  This is the
   only correctness surprise found in this evaluation and it is worth writing
   down whether or not the rest happens.
4. **Leave `CASRing` where it is.**  `CASAlgebra C A extends CASRing A`; do not
   define `CASRing R := CASAlgebra Int R`.  The instance-resolution cost falls on
   every goal, and every goal in the library today has integer coefficients.
5. **The fraction-field route needs a different class, not a bigger one.**
   `CASRingRat`'s inverse cannot generalise; what generalises is cancellation,
   under an `IsDomain`-style hypothesis, and it loses the divisibility shape.
   That is a real piece of design and should not be smuggled in as a field of a
   class introduced for another purpose.

The measurement is the surprise worth keeping: the extra polynomial layer is not
a tax.  On the asymmetric shape this repository's consumers actually have, it is
a 3.5x speed-up.  If `CASAlgebra` is ever built, it should be built for that
reason -- kernel throughput on tall towers -- and not because an identity in
`ℚ[ξ][X, z]` cannot otherwise be stated.  It can.
