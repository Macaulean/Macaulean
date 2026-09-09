/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.M2Cert

/-!
# Tests for `m2cert` / `m2cert?`

These **run Macaulay2**: the tactic starts the `m2/macaulean.m2` server the
same way `m2idealmem` does, so `M2` has to be on the path and `lake` has to be
run from the repository root.  The Macaulay2-free half of the story --
`poly_cert` on committed cofactors, including the exact text `m2cert?` prints
below -- is in `MacauleanTest/PolyCert.lean`, which imports none of this.

`stderrAsMessages` is off because the Macaulay2 plumbing traces its progress
with `dbg_trace`; without this the traces would land in `#guard_msgs`.
-/

set_option stderrAsMessages false

namespace MacauleanTest.M2Cert

/-! ## S1: divisibility, `g ∣ f` -/

/-- A cubic generator and a quadratic quotient: Macaulay2 has to divide, not
just recognise a factor. -/
theorem dvd_cubic (x y z : Int) :
    (x ^ 3 + y * z - 2) ∣ ((x ^ 3 + y * z - 2) * (x * y + 3 * z ^ 2 - 1)) := by
  m2cert

/-- The same divisibility with the product already expanded, so that nothing
about the goal's *shape* gives the quotient away. -/
theorem dvd_expanded (x y z : Int) :
    (x ^ 3 + y * z - 2) ∣
      (x ^ 4 * y + 3 * x ^ 3 * z ^ 2 - x ^ 3 + x * y ^ 2 * z + 3 * y * z ^ 3
        - y * z - 2 * x * y - 6 * z ^ 2 + 2) := by
  m2cert

/-! ## S2: ideal membership, `p = r` from `hᵢ : gᵢ = 0` -/

theorem mem_two_gens (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert [h1, h2]

/-- The `p = 0` special case, i.e. what `m2idealmem` does, with a determinantal
ideal of six generators. -/
theorem mem_six_gens (a b c d e f : Rat)
    (f1 : e ^ 2 - d * f = 0) (f2 : c * e - b * f = 0) (f3 : c * d - b * e = 0)
    (f4 : c ^ 2 - a * f = 0) (f5 : b * c - a * e = 0) (f6 : b ^ 2 - a * d = 0) :
    c ^ 2 * d - 2 * b * c * e + a * e ^ 2 + b ^ 2 * f - a * d * f = 0 := by
  m2cert [f1, f2, f3, f4, f5, f6]

/-! ## S3: `QQ` cofactors that are not integral

Generators with non-unit leading coefficients make Macaulay2 actually divide,
and over `QQ` the cofactors come back with denominators.  `m2cert` clears them
by scaling the whole certificate by their least common denominator, checking
the *integer* identity in the kernel, and cancelling the scale factor through
`Rat`'s `Macaulean.CASRingRat` instance.  Nothing about the goal or the call
says any of this happened.
-/

/-- Cofactor `(x² + z)/3`: one denominator. -/
theorem mem_scaled (x y z : Rat) (h1 : 3 * x * y - 3 * z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert [h1, h2]

/-- Cofactors `1/3` and `1/2`: *one* scale factor for the whole certificate,
their lcm, not one per cofactor. -/
theorem mem_scaled_lcm (x y z : Rat)
    (h1 : 3 * (x * y - z) = 0) (h2 : 2 * (y ^ 2 - x) = 0) :
    x * y - z + y ^ 2 - x = 0 := by
  m2cert [h1, h2]

/-! ## S4: ring variables that are not free variables

A ring variable is any maximal non-arithmetic subterm -- exactly what the
reflective half already treated as an atom -- so an application is a variable
on the same footing as a local, and the two halves cannot disagree about which
is which.  Mathlib is not available in this repository, so the motivating case,
a goal in `MvPolynomial (Fin 3) ℚ` whose variables are `MvPolynomial.X 0`,
`X 1`, `X 2`, cannot be written here.  `X` below is the closest thing that can:
an opaque constant applied to numerals, which reifies through the same code
path.
-/

/-- Opaque, so nothing about these terms is arithmetic and nothing unfolds:
`f x` and `g x y` are atoms and stay atoms. -/
opaque f : Rat → Rat
/-- A two-argument atom head. -/
opaque g : Rat → Rat → Rat
/-- Applied to a numeral, in the shape `MvPolynomial.X 0` has. -/
opaque X : Nat → Rat

/-- The same certificate as `mem_two_gens`, with `f x`, `g x y`, `f y` in place
of `x`, `y`, `z`.  Nothing in the tactic call says the variables are
applications. -/
theorem app_atoms (x y : Rat)
    (h1 : f x * g x y - f y = 0) (h2 : g x y ^ 2 - f x = 0) :
    f x ^ 3 * g x y + f x * g x y * f y + 5 = f x ^ 2 * f y + f y ^ 2 + 5 := by
  m2cert [h1, h2]

/-- Variables applied to numerals, and *no* free variables in the goal at all
-- the old round trip, which looked for `fvar`s, had nowhere to put these. -/
theorem numeral_arg_atoms (h1 : X 0 * X 1 - X 2 = 0) (h2 : X 1 ^ 2 - X 0 = 0) :
    X 0 ^ 3 * X 1 + X 0 * X 1 * X 2 + 5 = X 0 ^ 2 * X 2 + X 2 ^ 2 + 5 := by
  m2cert [h1, h2]

-- The `in [...]` clause is the atoms, pretty-printed, in first-occurrence order.
/--
info: Try this:
  [apply] poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [f x, g x y, f y] using [h1, h2]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_app_atoms (x y : Rat)
    (h1 : f x * g x y - f y = 0) (h2 : g x y ^ 2 - f x = 0) :
    f x ^ 3 * g x y + f x * g x y * f y + 5 = f x ^ 2 * f y + f y ^ 2 + 5 := by
  m2cert? [h1, h2]

/--
info: Try this:
  [apply] poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [X 0, X 1, X 2] using [h1, h2]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_numeral_arg_atoms
    (h1 : X 0 * X 1 - X 2 = 0) (h2 : X 1 ^ 2 - X 0 = 0) :
    X 0 ^ 3 * X 1 + X 0 * X 1 * X 2 + 5 = X 0 ^ 2 * X 2 + X 2 ^ 2 + 5 := by
  m2cert? [h1, h2]

-- …and those two lines, pasted verbatim.  This is the whole point of printing
-- them: the atoms have to re-elaborate to the same terms, or the reflective
-- check would be looking at a different identity.
theorem pasted_app_atoms (x y : Rat)
    (h1 : f x * g x y - f y = 0) (h2 : g x y ^ 2 - f x = 0) :
    f x ^ 3 * g x y + f x * g x y * f y + 5 = f x ^ 2 * f y + f y ^ 2 + 5 := by
  poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [f x, g x y, f y] using [h1, h2]

theorem pasted_numeral_arg_atoms
    (h1 : X 0 * X 1 - X 2 = 0) (h2 : X 1 ^ 2 - X 0 = 0) :
    X 0 ^ 3 * X 1 + X 0 * X 1 * X 2 + 5 = X 0 ^ 2 * X 2 + X 2 ^ 2 + 5 := by
  poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [X 0, X 1, X 2] using [h1, h2]

/-! ## What `m2cert?` prints

The variables are indexed by first occurrence, left to right, so the `in [...]`
clause and the exponent positions are the same on every run; the monomials are
in Macaulay2's own (grevlex) emission order.
-/

/--
info: Try this:
  [apply] poly_cert ["1.1.0.1 0.0.1.2 0.0.0.-3"] in [x, y, z]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_dvd (x y z : Int) :
    (x ^ 2 * y - z + 1) ∣ ((x ^ 2 * y - z + 1) * (x * y + 2 * z - 3)) := by
  m2cert?

/--
info: Try this:
  [apply] poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [x, y, z] using [h1, h2]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_mem (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert? [h1, h2]

-- A scaled certificate prints its denominator, so the paste proves the same
-- thing by the same route.
/--
info: Try this:
  [apply] poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] / 3 in [x, y, z] using [h1, h2]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_scaled (x y z : Rat) (h1 : 3 * x * y - 3 * z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert? [h1, h2]

-- `2/6` and `3/6`, i.e. `1/3` and `1/2`.
/--
info: Try this:
  [apply] poly_cert ["0.0.0.2", "0.0.0.3"] / 6 in [x, y, z] using [h1, h2]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_scaled_lcm (x y z : Rat)
    (h1 : 3 * (x * y - z) = 0) (h2 : 2 * (y ^ 2 - x) = 0) :
    x * y - z + y ^ 2 - x = 0 := by
  m2cert? [h1, h2]

/-! ## `+native` is opt-in, explicit, and loud -/

/--
warning: the reflective certificate is checked by `decide +native`: the proof depends on `Lean.ofReduceBool` -- which this toolchain records as a generated `._native.decide.ax` axiom -- so the Lean compiler and its runtime are part of its trusted base.  Drop `+native` to have the kernel check it.
-/
#guard_msgs in
theorem mem_native (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert +native [h1, h2]

-- The flag is carried into the printed replacement, so pasting it does not
-- silently change what checks the certificate.
/--
warning: the reflective certificate is checked by `decide +native`: the proof depends on `Lean.ofReduceBool` -- which this toolchain records as a generated `._native.decide.ax` axiom -- so the Lean compiler and its runtime are part of its trusted base.  Drop `+native` to have the kernel check it.
---
info: Try this:
  [apply] poly_cert +native ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [x, y, z] using [h1, h2]
  (the cofactors are Macaulay2's, in its emission order; pasting this keeps Macaulay2 out of the build)
-/
#guard_msgs in
theorem suggest_native (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  m2cert? +native [h1, h2]

/-! ## Axioms

The kernel path adds nothing beyond Lean's own three; `+native` adds the
generated native-evaluation axiom, which is what makes it worth refusing by
default.
-/

/-- info: 'MacauleanTest.M2Cert.dvd_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_cubic

/-- info: 'MacauleanTest.M2Cert.mem_two_gens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_two_gens

/-- info: 'MacauleanTest.M2Cert.mem_six_gens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_six_gens

-- The scaling path adds nothing either: `CASRingRat.cancel` is an ordinary
-- theorem, and the identity the kernel checked is an integer one.
/-- info: 'MacauleanTest.M2Cert.mem_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_scaled

/-- info: 'MacauleanTest.M2Cert.mem_scaled_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_scaled_lcm

-- Application atoms add nothing either: `f`, `g` and `X` are `opaque`, so they
-- carry `Classical.choice` in already, and no further axiom appears.
/--
info: 'MacauleanTest.M2Cert.app_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms app_atoms

/--
info: 'MacauleanTest.M2Cert.numeral_arg_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms numeral_arg_atoms

/--
info: 'MacauleanTest.M2Cert.pasted_app_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pasted_app_atoms

/--
info: 'MacauleanTest.M2Cert.pasted_numeral_arg_atoms' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pasted_numeral_arg_atoms

/--
info: 'MacauleanTest.M2Cert.mem_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 mem_native._native.decide.ax_1_1]
-/
#guard_msgs in
#print axioms mem_native

/-! ## Failure -/

-- The generators do not put `p - r` in the ideal, and the tactic says so rather
-- than leaving a goal behind.
/--
error: Tactic `m2cert` failed: the remainder modulo the given generators is not zero, so the goal does not follow from them

x y z : Rat
h1 : x * y - z = 0
⊢ x ^ 3 * y + x * y * z + 5 = 0
-/
#guard_msgs in
example (x y z : Rat) (h1 : x * y - z = 0) : x ^ 3 * y + x * y * z + 5 = 0 := by
  m2cert [h1]

end MacauleanTest.M2Cert
