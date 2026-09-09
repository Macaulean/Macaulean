# The polynomial representation and the reflective kernel path

`Macaulean.Polynomial R n` and the `algebra_norm_reflect` tactic exist to close
one kind of goal: a polynomial identity `A * B = Q * G + R` in a commutative
ring, at the size a computer-algebra certificate actually has (hundreds to
thousands of monomials in the expanded product).  The whole certificate is
checked by the Lean **kernel** by default -- never `native_decide`, and
`+native` only when the caller writes it out (see "`m2cert`" below) -- so
everything on the path has to be something the kernel can unfold, and cheaply.

This note records what the representation is, what the kernel does with it, and
what each change to it was worth.

## The representation

A monomial in `n` variables is a single `Nat`:

```lean
structure Mon (n : Nat) where
  key : Nat
```

`key` is the base-`Mon.base n` numeral whose little-endian digits are the
**partial sums** of the exponents:

```
x0^e0 · x1^e1 ⋯ x(n-1)^e(n-1)   ↦   S1 = e0,  S2 = e0+e1,  …,  Sn = e0+⋯+e(n-1)
```

so the most significant digit is the total degree.  `Mon.base n = 2 ^ bits n`
with `bits n = max 8 (62 / max 1 n)`: a power of two, so digit arithmetic is
GMP shifts and masks, and small enough that a whole key stays under `2^62` --
Lean's small-`Nat` fast path -- for `n ≤ 7`.  The tactic checks that natively
before emitting anything and *warns* (rather than fails) past it: the
certificate is then slow, not wrong.

Two facts make this the right packing, and both are proved in
`Macaulean/Polynomial/Key.lean`:

* **partial sums are additive**, so multiplying monomials is `key₁ + key₂`
  (`Mon.encodeFrom_add`) -- one kernel `Nat.add`;
* **comparing keys as `Nat`s is exactly grevlex** (`Mon.compare_encodeKey`):
  degree first, then reverse-lexicographic with the swap.  So ordering two
  monomials is one `Nat.blt`.

`Mon.grevlex` is spelled `bif Nat.beq … then .eq else bif Nat.ble … then .lt
else .gt`, deliberately not `compare`: `compare` goes through `Decidable`
instances, so the kernel would build -- and the whnf cache would retain -- a
`Nat.le` proof term at every monomial comparison, and the merge does nothing
but compare monomials.  `Mon.grevlex_eq_compare` says the two agree, and
`Mon.grevlex_eq_grevlexSpec` says key comparison **is** the classical grevlex
order on exponent vectors, so the order-theoretic instances (`Asymm`, `Irrefl`,
`Trichotomous`, `Trans`, `OrientedCmp`, `LawfulEqCmp`) are the `Nat` ones
pulled back along an injection.

Packing is faithful only while no digit overflows.  `Mon.mul` stays total (it
just adds keys) and the side condition is carried as `Polynomial.TermsOk` and
checked in the kernel by `Polynomial.mulOk`.  `Mon.wf` -- the `Bool` that says
a key really is the packing of its own exponent vector -- is one walk down the
key's digits (`Mon.wfFrom`: they must be non-decreasing, and there must be at
most `n` of them), and `Mon.degB` reads the total degree off the same walk as
its last digit.  Neither decodes the key into a list.

A polynomial is a `List (PolyTerm R n)` in strictly descending grevlex order;
`PolyTerm` is a coefficient and a `Mon n`.

## The kernel path

`algebra_norm_reflect` on a goal `lhs = rhs` in `A`:

1. **reify** both sides into `AlgExpr Int` constructor trees plus a context of
   atoms (`Macaulean/Grind/AlgPoly/Reify.lean`).  The tree mirrors the source
   term node for node, which is what makes step 3 hold definitionally;
2. **certificate**: close `AlgExpr.checkPolyEq nv lhs rhs = true` with
   `decide +kernel`;
3. **bridges**: `AlgExpr.denote (intDenote A) ctx e = goalSide`, both sides, by
   handing `Eq.refl` *ascribed to the equation* to the kernel through
   `mkAuxLemma` -- the same trick `decide +kernel` uses.  The kernel then does
   the defeq check with full unfolding, which is 200-300x cheaper than asking
   `Meta.isDefEq` to do it at the ambient transparency.  On the largest
   benchmark the two bridges are a few hundred ms out of 15 s;
4. **chain** the three with `AlgExpr.eq_of_checkPolyEq`.

`checkPolyEq` is what the kernel actually runs:

```lean
def checkPolyEq (nv : Nat) (e₁ e₂ : AlgExpr Int) : Bool :=
  match toPoly nv e₁.rebalance, toPoly nv e₂.rebalance with
  | some p, some q => Polynomial.removeZeros p.terms == Polynomial.removeZeros q.terms
  | _, _ => false
```

* `AlgExpr.rebalance` re-associates every `+`/`-` chain into a balanced tree of
  the same summands (reading `a - b` as `a + (-b)`, so mixed chains flatten
  too).  A polynomial written out monomial by monomial arrives as a
  *left-nested* chain, and evaluating that left to right merges a one-term list
  into an ever-growing sorted list once per monomial -- `O(m²)`.  Balanced, the
  same merges cost `O(m log m)`.  `AlgExpr.denote_rebalance` says the rewriting
  is denotation-preserving, which is all soundness needs.
* `AlgExpr.toPoly` is structurally recursive, so the kernel can unfold it.
  `none` means either a variable index `≥ nv` (which the tactic never produces)
  or a product whose exponents would overflow the packed key.  Nothing on this
  path ever calls `sortTerms`: `List.mergeSort` is well-founded recursion and
  the kernel cannot unfold it.
* every `add` and `mul` bottoms out in `mergeTermsF`, a **fuel-indexed**
  structural merge of two descending term lists.  Fuel only bounds the
  recursion depth actually taken, so the `1000000000` literal costs nothing
  (the kernel decrements a `Nat` literal, a GMP subtraction).  Its fuel-0
  fallback is the well-founded reference `mergeTermsSpec`, so
  `mergeTermsF f = mergeTermsSpec` for *every* fuel and no lemma downstream
  carries a fuel side condition.
* `removeZeros` runs **once**, here, and nowhere else.  `add` and `mul`
  preserve the descending order but leave the zero coefficients that
  cancellation produces; stripping them after every operation costs a traversal
  of the whole accumulated polynomial per step, which on a sum of `m` monomials
  is a second `O(m²)`.  One pass at the end is enough: two sorted term lists
  with the same nonzero terms become the same list, and a plain `BEq` is then
  decisive.

Soundness (`AlgExpr.eq_of_checkPolyEq`) needs only one direction: equal normal
forms denote equally, because `φ 0 = 0`.  It has **no degree side condition** --
that is what `mulOk` and the `Option` in `toPoly` buy.  Whether equal
expressions *do* reach equal normal forms is completeness, and that is what the
sortedness invariants (`Polynomial.sorted_add`, `Polynomial.sorted_mul`) are
for.

`#print axioms` on `AlgExpr.eq_of_checkPolyEq` and on every benchmark theorem:
`[propext, Classical.choice, Quot.sound]`.

Step 2 is the only place a caller can change the trusted base:
`algebra_norm_reflect +native` runs it as `decide +native` instead.  That is
opt-in, warns, and is described under "`m2cert`" below.

## Measured: kbench across the branch

`MacauleanTest/AlgebraNormPerf.lean`, `set_option Elab.async false`, four
certificate-shaped identities `A * B = Q * G + R` over `(x y z : Rat)` whose
expanded products have 41 / 296 / 755 / 1350 monomials.  "tactic" is reify +
kernel certificate + bridges; the final `addDecl` typecheck of the assembled
proof is 11 / 63 / 163 / 341 ms and has not moved across any of these changes.
Peak RSS is for the 1350-monomial run.

| representation / change | 41 | 296 | 755 | 1350 | RSS |
|---|---|---|---|---|---|
| `Mon n` an exponent list, `Mon.grevlex` comparing lists | 271 | 6768 | 38513 | 114446 | 34.5 GB |
| packed key, `Nat.beq`/`Nat.ble` instead of `compare` | 193 | 3498 | 19139 | 58105 | 20.6 GB |
| key comparison inlined into `mergeTermsF` | 189 | 3330 | 17887 | 54997 | 19.9 GB |
| one `removeZeros`, in `checkPolyEq` | 153 | 2447 | 13780 | 36104 | 14.3 GB |
| balanced `+`/`-` chains (`AlgExpr.rebalance`) | 156 | 1741 | 7899 | 16876 | 7.3 GB |
| digit-walk packing guard (`Mon.wfFrom`, `Mon.degB`) | 139 | 1581 | 7391 | 15795 | 7.0 GB |
| coefficient map from `CASRing`, not `intDenote` | **140** | **1604** | **7440** | **15917** | **7.0 GB** |

(ms of tactic time.  Run-to-run spread on the same binary is about 5%: the
`removeZeros` row re-measured as 156 / 2420 / 13401 / 35483 and 14.2 GB
immediately before the balanced-chain change.  The last row is not a change to
the representation at all: taking the coefficient map from the ambient ring's
`CASRing` instance puts two structure projections at the head of `φ`, and the
kernel unfolds a projection-of-constructor cheaply and whnfs the head once.)

Reference points on the same machine and identities: packing the key but still
comparing with `compare` put 1350 at 71541 ms; a Kronecker-packed
`List (Nat × Int)` with no `PolyTerm`/`Mon` structures and no `Grind.CommRing`
coefficient projections does the four in 196 / 2773 / 15009 / 38295 ms, so the
current representation is 2.4x faster than that at the largest size.

## Measured: where the remaining time goes

Found with a kernel micro-harness that times the individual steps of the
certificate (`decide +kernel` on `Nat.blt <step> 0`, one measurement per
`addDecl`) and compares each against the corresponding step of the
Kronecker-packed reference.  On the 755-monomial identity, whole check 7.1 s
(reference 9.4 s):

| step | ms |
|---|---|
| left side `A * B` | 3565 |
| of which the product `mulTerms` itself | 3330 (reference 4175) |
| right side `Q * G + R` | 2886 |
| of which building the 524-monomial remainder `R` | 935 |
| final `removeZeros` | 43 |
| final `BEq` | 48 |

The one item still worth more than 3%: the packing guard.  Stubbing
`Polynomial.mulOk` out entirely saves 12% of the check, because it is
re-verified at each of the ten-or-so products a single monomial is built from.
Removing it would mean bounding the total degree of the whole `AlgExpr` once,
up front, and carrying `TermsOk` through `denote_toPoly` as an invariant.

Measured and **rejected**:

* the `PolyTerm`/`Mon` structures.  A rewrite of the whole pipeline over bare
  `List (Nat × Int)` pairs, with no structure projections at all, was worth
  1.6%: the kernel unfolds a projection-of-constructor cheaply.
* the `Lean.Grind.CommRing Int` coefficient operations.
  `Semiring.toAdd (Ring.toSemiring (CommRing.toRing Grind.instCommRingInt))`
  whnfs to `{ add := Int.add }` in one step, not through a chain; a 2000-step
  kernel loop of `a + b` through the instance costs 36 ms against 26 ms for
  `Int.add` directly, and 33 vs 26 ms for `*` -- a difference swamped by the
  rest of a merge step.
* `Mon.fromVar` / `fromVarPower`, which run `List.ofFn` and `encodeKey` per
  variable occurrence.  Replacing them by a literal key is worth 3% of building
  an operand and 0.5% of the whole check.
* a balanced tree for `mulTerms`' inner accumulation.  Merging `p` rows of
  length `q` left to right costs about `p · N` steps and balanced costs about
  `p · q · log p`; at `p = q = 113`, `N = 755` those are 85k and 89k, i.e. the
  same.  Balancing only pays when the summands are *singletons*, which is
  exactly the sum-of-monomials case that `AlgExpr.rebalance` handles.

## `CASRing`: one instance per ring, for all of it

`algebra_norm_reflect`, `poly_cert` and `m2cert` each used to hard-wire three
ring-specific decisions: coefficients are `Int` literals mapped by
`Macaulean.intDenote`, the Macaulay2 base ring is whatever the ambient type
happens to have an `MRDI` instance for, and a `Dvd` goal unfolds the way `Int`'s
instance does.  `Macaulean/CASRing.lean` collects them into one class:

```lean
class CASRing (R : Type) extends Lean.Grind.CommRing R where
  ofInt : Int → R
  ofInt_isCoeffHom : Polynomial.IsCoeffHom ofInt
  m2BaseRing : M2BaseRing        -- `.ZZ` or `.QQ`
```

Declare one instance and every tactic in the library works on goals over `R`.
Extending `Lean.Grind.CommRing` means `[CASRing R]` alone meets the reflective
layer's instance needs; `CASRing.toCommRing` is registered at priority 100, so
`Grind.CommRing Rat` still resolves to `Grind.instFieldRat.toCommRing` and
nothing downstream sees a new instance path.  The kernel carrier stays `Int` on
purpose, for the `Nat.gcd` reason above.

Two things are deliberately *not* fields.

* **Variables and atoms.**  `Reify` treats anything it does not recognise as
  arithmetic as an atom, up to definitional equality, so `MvPolynomial.X i` and
  `Polynomial.X` need no help: they become variables of the reified expression
  and the normal forms compare as they should.  A hook would have no caller.
  Since the Macaulay2 half now shares that classifier
  (`Reify.classify`, `Reify.AtomState`) rather than looking for free
  variables of its own, this holds on both sides of the wire.
* **`Dvd`.**  `poly_cert` unfolds `g ∣ f` with `whnf`.  Both the instance Lean
  core gives and Mathlib's `semigroupDvd` are literally
  `⟨fun a b => ∃ c, b = a * c⟩`, so the `∃` is definitional.
  `MacauleanTest/PolyCert.lean` writes that instance out for `Rat` (core gives
  `Rat` no `Dvd`) and closes a divisibility goal through it, which is the check.

### Rational cofactors: `CASRingRat` and `/ d`

Macaulay2 over `QQ` routinely returns cofactors with denominators.  Rather than
put `Rat` in the kernel, the certificate is **scaled**: `m2cert` takes the least
common denominator `d` of all the cofactors at once, the kernel checks the
integer identity

```
d * (p - r) = q₁' * g₁ + ⋯ + q_k' * g_k        (ideal membership)
d * f       = g * q'                           (divisibility)
```

with `qᵢ' = d * qᵢ` integral, and `d` is cancelled afterwards.  Cancelling is
the one thing an arbitrary commutative ring cannot do, so it is an optional
second class:

```lean
class CASRingRat (R : Type) extends CASRing R where
  invOfInt : Int → R
  mul_invOfInt : ∀ d : Int, d ≠ 0 → CASRing.ofInt d * invOfInt d = 1
```

An inverse rather than a bare cancellation law, because cancellation alone does
not serve the divisibility shape: `g ∣ f` wants a *witness*, and the witness is
`q'/d`.  With the inverse both lemmas are three lines
(`CASRingRat.cancel`, `CASRingRat.dvd_witness`) and cancellation is one of
them.  `invOfInt` is a plain function, not an `Inv R`: the motivating rings
(`MvPolynomial (Fin 3) ℚ`) are not fields, they merely contain `ℚ`.

In the tactic the scale factor is written `poly_cert […] / d`, with **one**
denominator for the whole invocation rather than one per cofactor -- the
integer identity has to be scaled by the common multiple anyway, so a
per-cofactor denominator buys nothing and only makes the printed line harder to
read.  `m2cert?` prints it:

```
Try this:
  poly_cert ["0.0.0.2", "0.0.0.3"] / 6 in [x, y, z] using [h1, h2]
```

(cofactors `2/6` and `3/6`, i.e. `1/3` and `1/2`).  A ring with no
`CASRingRat` instance gets a message naming the class rather than a failed
check; `Int` is such a ring and does not need one, because `ZZ` cofactors are
integral.

### The instances shipped, and the one a Mathlib consumer writes

`Macaulean/CASRing.lean` ships `CASRing Int` (`ZZ`) and `CASRingRat Rat`
(`QQ`), plus two helpers: `CASRing.ofGrindCommRing R base`, which fills
`ofInt` with `intDenote R` and its proof with `intDenote_isCoeffHom R`, and
`CASRingRat.ofGrindField R`, for an honest `Lean.Grind.Field` of characteristic
zero.

A generic `[Grind.CommRing R] → CASRing R` *instance* is deliberately not
shipped: together with the `CASRing.toCommRing` projection instance it closes
a synthesis loop.  A ring without an instance is not turned away, though --
`AlgPoly.Tactic.casRingData` builds `CASRing.ofGrindCommRing A` on the spot,
so every goal that worked before the class exists still works, with the same
certificate.

The instance a Mathlib project working in `MvPolynomial (Fin 3) ℚ` would write
is this.  **It is not compiled here** -- this repository does not depend on
Mathlib -- so the lemma names may need adjusting; the shape is the point, and
every field is something Mathlib provides.

```lean
import Mathlib
import Macaulean.M2Cert

open Macaulean

noncomputable instance : CASRingRat (MvPolynomial (Fin 3) ℚ) where
  -- `ofInt`, its ring-map proof and the `Grind.CommRing` parent all come from
  -- Mathlib's `CommRing` instance, through grind's canonical `Int` map.
  toCASRing := CASRing.ofGrindCommRing (MvPolynomial (Fin 3) ℚ) .QQ
  -- `1/d` lives in the coefficient field; `C` puts it in the ring.
  invOfInt d := MvPolynomial.C ((d : ℚ)⁻¹)
  mul_invOfInt d hd := by
    have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
    show (Lean.Grind.CommRing.denoteInt d : MvPolynomial (Fin 3) ℚ)
        * MvPolynomial.C ((d : ℚ)⁻¹) = 1
    rw [Lean.Grind.CommRing.denoteInt_eq, ← map_intCast (MvPolynomial.C (σ := Fin 3)),
      ← map_mul, mul_inv_cancel₀ hd', map_one]
```

`Int.cast_ne_zero` is the `CharZero` fact the task's "`Rat.cast_injective`"
stands for; `mul_inv_cancel₀` is the field's; `map_intCast`/`map_mul`/`map_one`
are `MvPolynomial.C` being a ring hom.  With that one declaration, `m2cert`,
`m2cert?`, `poly_cert` and `algebra_norm_reflect` all work on
`MvPolynomial (Fin 3) ℚ` goals, and Macaulay2 is asked over `QQ`.

## `m2cert`: getting the certificate from Macaulay2

The tactic above proves an identity it is *handed*.  Finding the identity --
the quotients `Qᵢ` of a division, the remainder -- is what Macaulay2 is for.
`Macaulean/M2Cert.lean` joins the two.

`m2idealmem` and `m2remainder` already did the Macaulay2 half; what they did
afterwards was `simp` on `Macaulean.Polynomial`'s denotation, and that is the
step that does not finish at certificate scale.  `m2cert` keeps the round trip
and replaces the closing step with the kernel certificate.

### The two goal shapes

```lean
-- divisibility: one generator, no hypotheses
example (x y z : Int) :
    (x ^ 3 + y * z - 2) ∣ ((x ^ 3 + y * z - 2) * (x * y + 3 * z ^ 2 - 1)) := by
  m2cert

-- ideal membership: `hᵢ : gᵢ = 0` as arguments
example (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert [h1, h2]
```

* **`g ∣ f`.**  Macaulay2 divides `f` by `g`.  The remainder has to vanish;
  then `f = g * q` is proved reflectively and `Exists.intro` finishes, since
  `g ∣ f` unfolds to `∃ c, f = g * c`.
* **`p = r` from `hᵢ : gᵢ = 0`.**  Macaulay2 divides `p - r` by the `gᵢ`.  The
  remainder has to vanish; then `p = r + Σ qᵢ gᵢ` is proved reflectively and the
  generators are peeled off one at a time with the hypotheses.  `p = 0` is the
  special case `m2idealmem` handles, and `quotientRemainder` already returns
  one cofactor per generator, so any number of generators works with no change
  to `m2/macaulean.m2`.

If the remainder is *not* zero the goal does not follow from the generators,
and the tactic says so rather than leaving something behind.

The cofactors are rebuilt as terms of the ambient ring by `poly_def`'s
`PolyBuilder`, so the identity that reaches `algebra_norm_reflect` is
term-for-term what a committed `poly_def` would have produced.  The kernel's
coefficients are integers -- the reflective path normalises over
`Polynomial Int nv`, and a `Rat` coefficient would drag `Nat.gcd`, an
out-of-line GMP call, onto the kernel's hot path -- so a `QQ` cofactor with a
denominator is *scaled*, not rejected; see "Rational cofactors" below.

### `m2cert?` and keeping Macaulay2 out of the build

`m2cert?` closes the goal *and* prints the invocation that closes it again
without Macaulay2:

```
Try this:
  poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [x, y, z] using [h1, h2]
```

The strings are `poly_def`'s `e₁.….eₙ.k` monomial format -- one exponent per
listed variable, then an integer coefficient -- in Macaulay2's own emission
order, and the variables are the goal's atoms in first-occurrence order (left
to right, starting from the dividend), so the same goal prints the same line
every time.  They are printed with `ppExpr`, and they have to elaborate back:
`m2cert?` refuses rather than print an atom with a loose bound variable, an
unassigned metavariable, or an inaccessible name in it.  `poly_cert` (`Macaulean/PolyCert.lean`)
imports neither `Macaulean.Macaulay2` nor `Macaulean.IdealMembership`, so a
file that has been through this once needs no M2 process, no M2 installation
and no network: **committing the data and calling `poly_cert` is the
recommended way to keep a computer algebra system out of a build.**
`MacauleanTest/PolyCert.lean` is that file for this repository -- its
`paste_*` theorems are the suggestions above, copied verbatim.

A cofactor may equally well be an ordinary term:

```lean
poly_cert [x ^ 2 + z, 0] using [h1, h2]
```

so a certificate that is already a named constant -- from `poly_def`, when the
ring's variables are constants rather than the goal's bound variables -- goes
in as `poly_cert [name, …]`.  A `poly_def` *declaration* cannot hold a
cofactor written in the goal's bound variables, because its body is a closed
term; that is why the printed suggestion uses the string form, which goes
through the same builder and yields the same term.

### `+native`: opt-in, and what it costs

```lean
m2cert +native [h1, h2]        -- also m2cert?, poly_cert, algebra_norm_reflect
```

`+native` closes the `checkPolyEq … = true` obligation with `decide +native`
instead of `decide +kernel`.  The Lean **compiler and its runtime** then stand
where the kernel stood: on this toolchain `#print axioms` grows a generated
`<thm>._native.decide.ax_1_1` axiom (older toolchains show `Lean.ofReduceBool`
directly) next to the usual `propext, Classical.choice, Quot.sound`.  Nothing
selects it automatically, no tactic here ever calls `native_decide`, and using
it always logs a warning naming the cost.  `m2cert?` carries the flag into what
it prints, so pasting the suggestion cannot silently change what does the
checking.

The kernel path adds no axioms at all: `[propext, Classical.choice, Quot.sound]`
on every `m2cert`/`poly_cert` theorem in `MacauleanTest`.

### The wire

`m2cert` shares the Macaulay2 plumbing with `m2idealmem`:
`m2QuotientRemainderRaw` (`Macaulean/IdealMembership.lean`) reifies the goal
polynomials, serialises them as `Macaulean.Polynomial R n` over MRDI, sends one
`quotientRemainder` request, and hands the reply back untouched;
`m2cert` reads the monomials straight out of it.  Integer coefficients travel
as decimal strings, like everything else on this wire -- a bare JSON number is
unreadable to `MRDI.m2`, whose `fromMRDI` recursion knows hash tables, strings
and lists only; a rational travels as a numerator/denominator pair of strings.

`R` above is the *coefficient* ring, `m2QuotientRemainderRaw`'s `coeffRing`
argument, and it is what the ambient ring's `CASRing.m2BaseRing` names -- `Int`
for `ZZ`, `Rat` for `QQ`.  It used to be the ambient ring itself, which is why
`m2cert` only ever worked over `Int` and `Rat`: those are the types with `MRDI`
instances.  It defaults to the ambient ring, so `m2idealmem` and `m2remainder`
are unchanged.

### What a ring variable is, on both sides

The two halves of the library agree, by construction, on what a variable is.
`Macaulean.AlgPoly.Reify.classify` is the single definition: `+`, `-`, `*`,
unary `-` and `^` with a literal exponent are operations; a numeral, a cast of
one, and `CASRing.ofInt` applied to a literal are coefficients; **everything
else is an atom** -- a maximal non-arithmetic subterm.  Atoms are identified up
to definitional equality (`Reify.mkAtom`, which scans the table with `isDefEq`)
and numbered by first occurrence, left to right.

`Reify.reify` turns that into an `AlgExpr Int` for the kernel;
`toPolynomialExpr` (`Macaulean/IdealMembership.lean`) turns the *same*
classification into a `Macaulean.Polynomial` for Macaulay2, which sees the
atoms as its own `a, b, c, …` at the matching positions.  Macaulay2 sends the
cofactors back as exponent vectors over those positions, `m2cert` rebuilds them
as terms over the atoms, and `algebra_norm_reflect` reifies the result --
which lands on the same atoms because it is the same classifier.

A free variable is not a special case: it is the atom that happens to be an
`fvar`.  A goal in `MvPolynomial (Fin 3) ℚ` whose variables are
`MvPolynomial.X 0`, `X 1`, `X 2` makes the round trip like any other, and so
does one over `f x`, `g x y`.  Before, `toPolynomialExpr?` looked for `fvar`s
and embedded everything else as an opaque *constant*, so such a goal could not
be serialized at all; that limitation is gone.

`MacauleanTest/M2Cert.lean`'s S4 section is the test.  Mathlib is not available
in this repository, so the `MvPolynomial` case itself cannot be written here;
the nearest thing that can -- an `opaque X : Nat → Rat` applied to numerals,
plus `f x` and `g x y` for opaque `f`, `g` -- goes through exactly the same
code path, with `m2cert`, with the printed `poly_cert` line pasted back, and
with `#print axioms` clean.


## What consumers notice

* `Mon.mk` takes a **key**, not an exponent list.  Build a monomial from
  exponents with `Mon.ofPowersN n p`; `Mon.powers` is now a *function* (it
  decodes the key), not a field, and every lemma that used to talk about the
  field talks about the function, so the statements are unchanged.
  `Macaulean/Polynomial/MRDI.lean` goes through `Mon.ofPowersN`.
* `simp [Mon.denote]` on a concrete monomial needs the `Mon.mon_powers_simproc`
  simproc as well, to compute `Mon.powers` on a literal key
  (`Macaulean/IdealMembership.lean` passes it).
* `add`, `sub`, `mul`, `smul`, `mulMon`, `pow`, `mulChecked`, `powChecked` and
  the `Add` / `Sub` / `Mul` / `NatPow` / `SMul` instances no longer take a
  `[BEq R]` argument.
* `add` and `mul` no longer strip zero coefficients.  `(p.sub p).terms` is a
  list of zero terms, not `[]`; compare `removeZeros (p.sub q).terms` with `[]`
  instead (see `MacauleanTest/PolyKernel.lean`).
  `normalize` and `Equiv` are unchanged (they still sort and strip), but they
  go through `List.mergeSort` and so are *not* kernel-reducible -- the
  reflective path deliberately never calls them.
* `mulChecked` / `powChecked` are the guarded forms, and `toPoly` answers
  `none` when a product would overflow the packed key, exactly as an
  out-of-range variable index already did.
* `algebra_norm_reflect` warns when an `nv`-variable key would exceed `2^62`.
* `algebra_norm_reflect` and `algebra_norm` take an optional `+native` flag.
  The kernel is still the default; `+native` warns.
* The coefficient map is no longer `Macaulean.intDenote` by fiat: it is
  `CASRing.ofInt` of the ambient ring's `Macaulean.CASRing` instance, or of
  `CASRing.ofGrindCommRing A` when it has none.  `intDenote` is still what
  those instances use; it now lives in `Macaulean/CASRing.lean`, which
  `Macaulean/Grind/AlgPoly/Expr.lean` imports, so the name and statement of
  `intDenote_isCoeffHom` are unchanged.
* `Reify` reifies an application of `CASRing.ofInt` to an integer literal as
  that *coefficient*, and `Reify.intLitValue?` reads the raw
  `Int.ofNat`/`Int.negSucc` constructor form that `Meta.getIntValue?` does not.
* `poly_cert` takes an optional `/ d` between the cofactor list and `in`;
  `PolyCert.closeDvd` and `PolyCert.closeEq` take the same as a trailing `Nat`
  argument, defaulting to 1.
* `M2Cert.CertPoly`'s coefficients are `Rat`, not `Int`, and
  `M2Cert.certify` returns the scale factor alongside the specs.
* `m2QuotientRemainderRaw` takes an optional `coeffRing`, the Macaulay2 base
  ring; `toPolynomialExpr` translates numerals and unary minus instead of
  embedding them as opaque constants, which is what lets it differ from the
  ambient ring.
* `Reify` exports the atom table (`AtomState`, `AtomM`, `mkAtom`,
  `collectAtoms`, `atomStateOf`) and the classifier (`Node`, `classify`); the
  Macaulay2 half uses them instead of its own free-variable scan.
  `toPolynomialExpr?` is now `toPolynomialExpr`, taking the variable count and
  running in `Reify.AtomM` rather than taking an `FVarIdMap Nat`;
  `m2QuotientRemainderRaw` lost its `sortVars` flag and returns the atoms as
  `Array Expr` rather than the free variables as `Array FVarId`, and so does
  `M2Cert.certify`.  `M2Cert.varName` became `M2Cert.atomText`, which
  pretty-prints an atom and refuses the ones that would not elaborate back.
* `AlgPoly.Tactic.proveEq lhs rhs native` builds the reflective proof of
  `lhs = rhs` and returns it without touching the goal state.  That is the
  entry point for tactics that state their own identity (`poly_cert`,
  `m2cert`); `solveGoal` is `proveEq` plus the assignment.
* `MrdiType Int` encodes an integer as a decimal *string* (and decodes either
  form).  A bare JSON number is unreadable to `MRDI.m2`.
* `m2QuotientRemainderRaw` is the Macaulay2 round trip on its own -- reify,
  serialise, one `quotientRemainder` request, reply untouched --
  with `m2QuotientRemainderImpl` the deserialisation that used to follow it.
* `AlgExpr.checkPolyEq` rebalances its arguments; if you call `toPoly` yourself
  on a hand-built chain and compare, do the same or expect `O(m²)`.
