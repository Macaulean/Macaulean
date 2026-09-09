# The polynomial representation and the reflective kernel path

`Macaulean.Polynomial R n` and the `algebra_norm_reflect` tactic exist to close
one kind of goal: a polynomial identity `A * B = Q * G + R` in a commutative
ring, at the size a computer-algebra certificate actually has (hundreds to
thousands of monomials in the expanded product).  The whole certificate is
checked by the Lean **kernel** -- never `native_decide`, never `+native` -- so
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
| digit-walk packing guard (`Mon.wfFrom`, `Mon.degB`) | **139** | **1581** | **7391** | **15795** | **7.0 GB** |

(ms of tactic time.  Run-to-run spread on the same binary is about 5%: the
`removeZeros` row re-measured as 156 / 2420 / 13401 / 35483 and 14.2 GB
immediately before the balanced-chain change.)

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
* `AlgExpr.checkPolyEq` rebalances its arguments; if you call `toPoly` yourself
  on a hand-built chain and compare, do the same or expect `O(m²)`.
