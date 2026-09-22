# Macaulean on `poly-repr-reflect`: an orientation

A reader's guide to this branch: what the code does, how the pieces fit, how to
run and benchmark it yourself, and an order in which to read it if you are also
using it to learn Lean.  Written 2026-09-22 against commit `ae03e33`, Lean
`v4.33.1`, Macaulay2 1.26.06 (Homebrew).  No Mathlib.

The two existing notes in this directory go much deeper and are written for
people already inside the design:

* [`poly-repr-reflect.md`](poly-repr-reflect.md) -- the monomial encoding, the
  kernel path, the measured cost of every optimisation, `CASRing`, `m2cert`;
* [`cas-algebra-evaluation.md`](cas-algebra-evaluation.md) -- whether to support
  polynomial *coefficients* (`ℚ[t][x,y]`); conclusion: not yet.

This note is the map you read before those.


## 1. What the project is for, in one paragraph

Macaulay2 is good at *finding* things (quotients, remainders, Gröbner bases,
factorizations); Lean is good at *checking* them.  The goal is Lean tactics that,
faced with a goal like "`p` lies in the ideal `(g₁, …, gₖ)`", ask Macaulay2 for a
certificate (cofactors `qᵢ` with `p = Σ qᵢ gᵢ`) and then prove the goal in Lean
from that certificate.  Macaulay2 is never trusted: if it returns garbage the
Lean check fails.  The hard part turned out not to be talking to Macaulay2 but
the *checking*: verifying a polynomial identity with thousands of monomials is
far too slow for `ring`/`simp`/`grind`.  Most of this branch is a fast checker
for exactly that.


## 2. The one idea you need: proof by reflection

A naive proof of `(x+y)^2 = x^2 + 2*x*y + y^2` rewrites the goal step by step
(`simp`, `ring`), and each step makes a proof term.  For thousands of monomials
that proof term is enormous.

Reflection does it differently:

1. Define a **data type of syntax**, `AlgExpr` (`Macaulean/Grind/AlgPoly/Expr.lean`):

   ```lean
   inductive AlgExpr (C : Type) where
     | coeff (k : C) | var (i : Nat)
     | add (a b : AlgExpr C) | sub (a b : AlgExpr C) | mul (a b : AlgExpr C)
     | neg (a : AlgExpr C) | pow (a : AlgExpr C) (k : Nat)
   ```

   and a function `denote` that turns such a tree back into an actual element of
   a ring `A`, given values for the variables (`ctx`) and a map `φ` for the
   coefficients.

2. Write an ordinary **program** `checkPolyEq : Nat → AlgExpr Int → AlgExpr Int → Bool`
   (`Macaulean/Grind/AlgPoly/PolyEval.lean`) that expands both trees into a
   normal form and compares them.

3. **Prove once, in general,** that the program is sound:

   ```lean
   theorem eq_of_checkPolyEq (nv : Nat) (e₁ e₂ : AlgExpr Int)
       (h : checkPolyEq nv e₁ e₂ = true) :
       e₁.denote φ ctx = e₂.denote φ ctx
   ```

4. For a specific goal, the tactic builds the two trees (**reification**), then
   proves `checkPolyEq nv lhs rhs = true` by `decide +kernel`, i.e. by letting
   Lean's *kernel* run the program.  The proof term is tiny; all the work is
   computation the kernel does while type-checking it.

5. It also has to show that `denote` of each tree really *is* the goal side
   (the "bridges").  Because the tree mirrors the source term node for node,
   this holds by `rfl` (definitional unfolding).

So the whole proof is `bridge⁻¹ · eq_of_checkPolyEq … (kernel computation) ·
bridge`.  See `proveEq` in `Macaulean/Grind/AlgPoly/Tactic.lean:206` -- it is
readable top to bottom and labelled 1, 2, 3.

**Why the kernel and not `native_decide`?**  `decide +native` compiles the
program to machine code and runs it -- much faster, but then the Lean compiler
is part of what you trust, and `#print axioms` shows an extra axiom.  This
project defaults to the kernel everywhere and only uses native evaluation when
you write `+native`, which warns.  The price is that everything the kernel
runs must be written so the kernel can *unfold* it cheaply, which explains most
of the odd-looking choices in `Macaulean/Polynomial/` (fuel-indexed recursion
instead of well-founded recursion, no `List.mergeSort`, monomials packed into a
single `Nat`, comparisons written with `Nat.ble` instead of `compare`).

You can check the trusted base yourself: every test theorem ends with
`#print axioms …` giving `[propext, Classical.choice, Quot.sound]`, the three
standard axioms of Lean's logic, and nothing else.


## 3. Map of the code

Roughly bottom to top.  Line counts are approximate.

### Talking to Macaulay2

| File | What it does |
|---|---|
| `Macaulean/Macaulay2.lean` (72) | Spawns `M2 --script ./macaulean.m2` in `./m2/` and talks JSON-RPC over its stdin/stdout, using LSP-style `Content-Length` framing.  One global process per Lean process (`globalM2Server`). |
| `m2/macaulean.m2` | The server side.  Registers methods `quotientRemainder`, `factorInt`, `factor`, `mrdiFactor`, `mrdiEcho`, `testMethod`.  Uses the M2 packages `JSONRPC`, `MRDI`, `JSON`. |
| `MRDI/Basic.lean`, `MRDI/Poly.lean`, `MRDI/Uuid.lean` | MRDI, the JSON serialization format shared with OSCAR, implemented in Lean. |
| `Macaulean/Polynomial/MRDI.lean` | MRDI encoding of this project's `Polynomial` type. |

### The polynomial representation (all kernel-evaluable)

| File | What it does |
|---|---|
| `Macaulean/Polynomial/Key.lean` (507) | A monomial `x0^e0 ⋯ x(n-1)^e(n-1)` is a single `Nat` whose base-`2^bits` digits are the *partial sums* `e0, e0+e1, …`.  Then monomial multiplication is `Nat` addition and grevlex comparison is `Nat` comparison.  Both facts are proved here. |
| `Macaulean/Polynomial/Basic.lean` (669) | `Mon n`, `PolyTerm R n`, `Polynomial R n` (a list of terms in descending grevlex order), `add`, `mul`, `pow`, `denote`. |
| `Macaulean/Polynomial/Lemmas.lean` (1469) | The correctness lemmas: sortedness preserved, `denote` of `add` is `+` of `denote`s, etc.  The largest file; mostly routine inductions. |
| `Macaulean/Polynomial/Hom.lean` (218) | `IsCoeffHom φ` (the coefficient map is a ring hom) and `denoteWith`, which is `denote` through such a map. |
| `Macaulean/Polynomial.lean` | Re-exports the above; the rest is commented-out older material. |

### The reflective checker

| File | What it does |
|---|---|
| `Macaulean/Grind/AlgPoly/Expr.lean` | `AlgExpr`, `denote`, and `rebalance` (re-associates long `+` chains into balanced trees: `O(m log m)` instead of `O(m²)`). |
| `Macaulean/Grind/AlgPoly/PolyEval.lean` | `toPoly`, `checkPolyEq`, and the soundness theorem `eq_of_checkPolyEq`. |
| `Macaulean/Grind/AlgPoly/Reify.lean` | Meta-level code: turns a Lean `Expr` into an `AlgExpr` tree.  `classify` decides what is an operation, a numeral, or an **atom** (anything else, e.g. `f x`, becomes a variable). |
| `Macaulean/Grind/AlgPoly/Tactic.lean` | The tactics `algebra_norm_reflect` and `algebra_norm`; `proveEq` is the whole pipeline. |
| `Macaulean/CASRing.lean` | The class `CASRing R` a ring declares to use all of this (coefficient map `Int → R`, and whether M2 should compute over `ZZ` or `QQ`).  `CASRingRat` adds `1/d`, so rational cofactors can be handled by scaling by a common denominator.  Instances for `Int` and `Rat`. |

### User-facing tactics

| Tactic | File | Needs M2? | Goal shape |
|---|---|---|---|
| `algebra_norm_reflect` | `Grind/AlgPoly/Tactic.lean` | no | polynomial identity `lhs = rhs` |
| `algebra_norm` | same | no | same, falls back to `grind` (so may use hypotheses) |
| `poly_def` | `PolyDef.lean` | no | *command*: defines a constant from a compact monomial string, e.g. `"2.0.0.3 0.1.1.-4"` = `3·a² − 4·b·c` |
| `poly_cert [...] in [...] using [...]` | `PolyCert.lean` | no | membership / divisibility, cofactors supplied by you |
| `m2cert [h₁, …]` | `M2Cert.lean` | yes | `p = r` from `hᵢ : gᵢ = 0`, or `g ∣ f` |
| `m2cert? [h₁, …]` | same | yes | same, and prints the `poly_cert` line that reproduces the proof without M2 |
| `m2idealmem [h₁, …]` | `IdealMembership.lean` | yes | `p = 0` -- the **older** path, closes with `simp`; slow at scale |
| `m2remainder [h₁, …]` | same | yes | older; leaves the remainder as a goal |
| `m2factor n`, `m2reducible` | `Factorization.lean` | yes | toy integer factorization demos |

The intended workflow is: write `m2cert?`, run it once, paste the printed
`poly_cert …` line in its place.  After that the file needs no Macaulay2 at all
(`MacauleanTest/PolyCert.lean` imports nothing from the M2 side, to prove the
point).

### Everything else

* `Main.lean` -- an early demo executable (`lake exe macaulean`); not used by the tests.
* `m2-benchmarks/`, `mes-benchmark*.m2` -- Macaulay2-side experiments.
* `paper/`, `Reports/`, `meetings/`, `QuarterlyReports/` -- project writing.
* `MacauleanTest/SumOfSquaresMike.lean` (untracked) imports `Macaulean.SumOfSquares`,
  which does not exist on this branch, so it will not compile here.


## 4. What happens during `m2cert [h1, h2]`

Goal: `x^3*y + x*y*z + 5 = x^2*z + z^2 + 5` with `h1 : x*y - z = 0`, `h2 : y^2 - x = 0`.

1. **Classify atoms** (`Reify.classify`): `x, y, z` become variables 0, 1, 2.
2. **Serialize** `p - r` and the `gᵢ` as MRDI JSON; send one
   `quotientRemainder` request (`m2QuotientRemainderRaw`,
   `Macaulean/IdealMembership.lean`).
3. **Macaulay2** divides and returns cofactors `q₁, q₂` and a remainder.  A
   nonzero remainder means the goal does not follow from these generators, and
   the tactic says so.
4. **Rebuild** the cofactors as Lean terms (`PolyBuilder`, `Macaulean/PolyDef.lean`).
   Over `QQ`, if they have denominators, multiply through by their lcm `d`.
5. **Prove** `p = r + q₁*g₁ + q₂*g₂` (times `d` if scaled) with the reflective
   checker of §2 -- this is where all the time goes.
6. **Peel off** each generator using `hᵢ` (`PolyCert.gen_step`:
   `a = d → g = 0 → a + c*g = d`), then cancel `d` if needed.

`poly_cert` is steps 4–6 with the cofactors typed in, which is why pasting
`m2cert?`'s output removes Macaulay2 from the build.


## 5. Running and testing it yourself

All commands from the **repository root**.  That matters: the Macaulay2 server is
started with the relative path `./m2/macaulean.m2`, so a Lean process started
elsewhere cannot find it.

### Build

```
lake build                 # the library (Macaulean, MRDI) and the demo exe
lake build MacauleanTest   # also the test modules
```

### What is cached

Lake compiles each module to `.lake/build/**/*.olean` and remembers its
messages.  A module is re-elaborated only when its source or something it
imports changes; otherwise lake prints `Replayed Foo` -- it re-prints the
*stored* messages and runs nothing.  So a second `lake build MacauleanTest` is
instant and **does not actually re-run the tests**.

To really run one test file:

```
lake env lean MacauleanTest/M2Cert.lean
```

`lake env lean` elaborates that one file from scratch every time, taking its
imports from the cached `.olean`s, and writes nothing.  Its output is the
file's messages; no output other than info/warnings means success.

### Results on this machine (2026-09-22)

All pass.  Wall-clock for `lake env lean <file>`, which includes about 0.5 s of
loading imports:

| File | s | Uses M2 | What it tests |
|---|---:|:-:|---|
| `Uuid` | 0.7 | | MRDI UUIDs |
| `Poly` | 1.1 | | `Polynomial` operations on small examples |
| `PolyKernel` | 0.7 | | `decide +kernel` on `Polynomial` ops |
| `PolyDef` | 0.7 | | the `poly_def` command |
| `AlgebraNorm` | 0.8 | | `algebra_norm_reflect` on small identities |
| `PolyCert` | 1.0 | | `poly_cert` with pasted certificates |
| `Factorization` | 1.2 | ✓ | `m2factor`, `m2reducible` |
| `IdealMembership` | 2.2 | ✓ | older `m2idealmem` path |
| `M2Cert` | 1.9 | ✓ | `m2cert`, `m2cert?`, scaling, atoms, failures |
| `Benchmarks` | 3.8 | ✓ | a 9-variable `m2idealmem` + `grind` |
| `TestGB5Pts` | 0.8 | | (body commented out) |

Many tests use `#guard_msgs`, which fails the file if a message differs from the
expected text written just above it.  That is how "`m2cert?` prints exactly this
line" is tested.

### Output that looks alarming but is not

* A long `HashTable{"architecture" => arm64 …}` dump, `Macaulean M2 Startup`,
  `Packages Loaded`, `SENDING REQUEST`, `Coefficients Returned`,
  `Macaulay2 Finished` -- Macaulay2's stderr and `dbg_trace` debugging output.
* `warning: algebra_norm_reflect: 2 variables need a 62-bit monomial key, past
  the kernel's small-Nat range` on every goal with one or two variables.  This
  is a **false alarm**: a key is always strictly less than `base^n`, which for
  `n ≤ 2` is `2^62`, but the check at `Macaulean/Grind/AlgPoly/Tactic.lean:229`
  tests `base^n < 2^62` and so fires at equality.  Real slowdown only starts at
  8 or more variables.
* Unused-variable linter warnings during `lake build`.

### In an editor (VS Code, Emacs `lean4-mode`, Zed)

All three drive the same Lean language server, so the behaviour is the same:

* Open the **repository root** as the project (for the `./m2/` path above).
* Run `lake build` in a terminal first.  The editor uses the built `.olean`s for
  imports; after you change a library file, open files report their imports are
  stale -- rebuild, then "Restart File".
* Editing re-elaborates from the edited point downward, not the whole file.
* Put the cursor inside a `by` block to see the goal; hover for types.  This is
  the best way to learn what each tactic step does.
* The Macaulay2 process is started once per Lean server process and reused.

### A scratch file

Anything outside the library works, e.g. a file in `Mike/` or `/tmp`,
elaborated with `lake env lean path/to/Play.lean` or opened in the editor:

```lean
import Macaulean

-- per-step timings of the reflective proof
set_option trace.macaulean.reflect true in
example (x y z : Int) : (x + y + z)^4 = (x + y + z)^2 * (x + y + z)^2 := by
  algebra_norm_reflect

-- ask Macaulay2, and get a line to paste that no longer needs it
example (x y : Rat) (h1 : x^2 - y = 0) (h2 : y^3 - 1 = 0) : x^6 = 1 := by
  m2cert? [h1, h2]
-- prints: poly_cert ["4.0.1 2.1.1 0.2.1", "0.0.1"] in [x, y] using [h1, h2]

example (x y : Int) : (x - y) ∣ (x^5 - y^5) := by
  m2cert?

theorem t (x y : Rat) : (x + y)^5 = (x + y)^2 * (x + y)^3 := by
  algebra_norm_reflect
#print axioms t   -- [propext, Classical.choice, Quot.sound]
```

The cofactor strings are `e₁.e₂.….eₙ.coeff` per monomial, space separated, one
exponent per listed variable: `"4.0.1 2.1.1 0.2.1"` in `[x, y]` is
`x⁴ + x²y + y²`.


## 6. Benchmarking

### The main benchmark

```
lake env lean MacauleanTest/AlgebraNormPerf.lean
```

Four identities `A * B = Q * G + R` over `x, y, z : Rat`, taken from a real
formalization project (reduction modulo a cubic), with expanded products of 41,
296, 755, 1350 monomials.  Not part of the test suite, because it is slow.  It
uses a `kbench` command (defined in that file) that builds the goal directly as
an `Expr` and reports:

* **tactic** -- reify + kernel certificate + bridges;
* **kernel** -- the final type-check of the finished proof when it is added to
  the environment.

Measured here (32 s total, peak memory 7.0 GB):

| identity | monomials | tactic ms | kernel ms | recorded in docs |
|---|---:|---:|---:|---:|
| `perf_hess_sq` | 41 | 177 | 15 | 140 |
| `perf_redH2_sq` | 296 | 2017 | 81 | 1604 |
| `perf_redH3_sq` | 755 | 8860 | 216 | 7440 |
| `perf_theta3_step` | 1350 | 18776 | 421 | 15917 |

About 20% slower than the recorded numbers (measured on another machine), and
the same shape: roughly quadratic in the monomial count, and almost all of the
time is the `decide +kernel` step.  `/usr/bin/time -l lake env lean …` gives the
peak memory (`maximum resident set size`).

Why `kbench` instead of ordinary source syntax: elaborating a several-hundred-
monomial expression *written in the source file* is itself slow -- the file
header says a 296-monomial statement took over 10 minutes just to elaborate.
For your own large examples use `poly_def` (or `kbench`), not literal syntax.

### Older speed tests

`MacauleanTest/MacauleanSpeedTest.lean` and `MacauleanTest/GrindSpeedTest.lean`
exercise the older `m2idealmem` + `grind` path on 9-variable problems.
`GrindSpeedTest` in particular proves a very large identity by plain `grind`
with `maxHeartbeats 10000000`, and can run for many minutes -- it is the
baseline the reflective path exists to beat.  `MacauleanSpeedTest` ends in a
`sorry`.

### The Macaulay2 side

`m2-benchmarks/` holds M2 scripts; run them with `M2 --script file.m2`.  Round
trip overhead is small in the tests above (M2 start plus a request is well under
a second); the kernel check dominates everything.


## 7. A reading path for learning Lean from this code

Ordered from concrete to meta.  Each step says which Lean ideas it shows.

1. **`MacauleanTest/PolyKernel.lean`** (46 lines).  Small polynomials built by
   hand and facts proved with `decide +kernel`.  *Ideas:* structures, `def`
   vs `theorem`, `decide`, `#print axioms`.
2. **`Macaulean/Grind/AlgPoly/Expr.lean`, lines 1–60.**  `AlgExpr` and
   `denote`.  *Ideas:* inductive types, structural recursion by pattern
   matching, type-class arguments `[Grind.CommRing A]`.
3. **`Macaulean/Polynomial/Hom.lean`, the top.**  `IsCoeffHom` is a
   `structure … : Prop` whose fields are proofs.  *Idea:* a proposition bundling
   several facts; compare with a `class`.
4. **`Macaulean/Grind/AlgPoly/PolyEval.lean`.**  `toPoly`, `checkPolyEq`, then
   `eq_of_checkPolyEq`.  The last proof is short and typical: `unfold`,
   `split at h` (case on the `match`), `rw [← …]` with earlier lemmas,
   `show` to restate the goal, `exact absurd h (by simp)` for the impossible
   branch.  Step through it in the editor with the cursor after each line.
5. **`Macaulean/Polynomial/Key.lean`.**  Real arithmetic proofs about `Nat`:
   `omega`, `calc` blocks, induction on lists.  Good for seeing how proofs about
   concrete encodings go.
6. **`Macaulean/Grind/AlgPoly/Tactic.lean`, `proveEq`.**  Your first tactic
   code.  *Ideas:* `Expr` (Lean terms as data), `mkAppN`, `mkConst`, the
   `TacticM` / `MetaM` monads, `evalTactic` with quoted syntax
   `` `(tactic| decide +kernel) ``, `elab "name" : tactic => …`.
7. **`Macaulean/Grind/AlgPoly/Reify.lean`.**  Walking an `Expr` and matching on
   `HAdd.hAdd` etc., with `isDefEq` to identify atoms.
8. **`Macaulean/PolyCert.lean`, then `Macaulean/M2Cert.lean`.**  Custom syntax
   (`syntax certList := " [" term,* "]"`), assembling a proof from lemmas like
   `gen_step`, and `Try this:` suggestions.
9. **`Macaulean/Macaulay2.lean`.**  `IO`, processes, streams, `initialize` for a
   global reference.  Mostly programming, not proving.

Some things to try, none of which need changes to the library:

* Change a number in one of `AlgebraNorm.lean`'s identities so it is false and
  see how `algebra_norm_reflect` fails.  It reports ``Tactic `decide` proved
  that the proposition Macaulean.AlgExpr.checkPolyEq 2 (…) (…) = true is
  false`` -- which conveniently prints the reified `AlgExpr` trees, so you can
  see exactly what reification (§2, step 4) produced from your goal.
* Prove the same small identity with `algebra_norm_reflect`, `grind`, and (if
  you add one) `simp`, and compare with `set_option trace.profiler true`.
* In a scratch file, `#eval` a `checkPolyEq` call directly on hand-built
  `AlgExpr` trees, then prove the same with `decide +kernel` and time it: the
  first is compiled code, the second the kernel -- the gap is the price of not
  trusting the compiler.
* Use `m2cert?` on an ideal-membership problem you know from Macaulay2 and paste
  the result back as `poly_cert`.
* Grow a `kbench`-style example until it gets slow, watching
  `trace.macaulean.reflect`.


## 8. Where things stand, and open threads

From the commit history and the two design notes:

* **Done on this branch:** packed monomials; kernel-evaluable merge;
  `algebra_norm_reflect` (about 7× faster than the first version, from 114 s
  to 16 s on the largest benchmark); `poly_def`, `poly_cert`, `m2cert`/`m2cert?`;
  `CASRing` so a new ring needs only one instance; rational cofactors by
  scaling; arbitrary atoms (e.g. `MvPolynomial.X i`) on both the Lean and M2
  sides.
* **Known remaining cost:** the kernel certificate is still roughly quadratic
  in size.  The note measures where the time goes on the 755-monomial case:
  about half the product `A*B`, about 40% the right-hand side.  The packing guard
  (`mulOk`) re-checked at each product is the one identified 12% saving not yet
  taken.
* **Evaluated and deferred:** polynomial coefficients (`CASAlgebra`).  An
  extra variable does the same job for now.  The evaluation found that a
  nested representation would be *faster*, and that `removeZeros`' zero test
  would be wrong for nested coefficients -- worth knowing if that is ever built.
* **Not compiled here:** the Mathlib `MvPolynomial (Fin 3) ℚ` instance shown in
  `poly-repr-reflect.md`; this repository has no Mathlib dependency.
* **Legacy:** `m2idealmem` / `m2remainder` close with `simp` and do not scale;
  `m2cert` replaces them.  `Factorization.lean` and `Main.lean` are early demos.
* **Minor:** the false 1–2-variable key-size warning (§5).
