/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.PolyCert
import Macaulean.PolyDef

/-!
# Tests for `poly_cert` — and for what `m2cert?` prints

This file imports `Macaulean.PolyCert` and `Macaulean.PolyDef` and **nothing
from the Macaulay2 side**: not `Macaulean.M2Cert`, not
`Macaulean.IdealMembership`, not `Macaulean.Macaulay2`.  Nothing here can start
an M2 process, so if these theorems compile then the certificates really are
checkable without a computer algebra system.

The `paste_*` theorems below are the `m2cert?` suggestions from
`MacauleanTest/M2Cert.lean` copied verbatim: same goals, same tactic text.
-/

namespace MacauleanTest.PolyCert

/-! ## The `m2cert?` output, pasted -/

/-- `m2cert?` on this goal printed `poly_cert ["1.1.0.1 0.0.1.2 0.0.0.-3"] in
[x, y, z]`; this is that line, unedited. -/
theorem paste_dvd (x y z : Int) :
    (x ^ 2 * y - z + 1) ∣ ((x ^ 2 * y - z + 1) * (x * y + 2 * z - 3)) := by
  poly_cert ["1.1.0.1 0.0.1.2 0.0.0.-3"] in [x, y, z]

/-- Likewise for the membership shape. -/
theorem paste_mem (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [x, y, z] using [h1, h2]

-- And with the flag carried through.
/--
warning: the reflective certificate is checked by `decide +native`: the proof depends on `Lean.ofReduceBool` -- which this toolchain records as a generated `._native.decide.ax` axiom -- so the Lean compiler and its runtime are part of its trusted base.  Drop `+native` to have the kernel check it.
-/
#guard_msgs in
theorem paste_native (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  poly_cert +native ["2.0.0.1 0.0.1.1", "0.0.0.0"] in [x, y, z] using [h1, h2]

/-! ## Scaled certificates, pasted

`m2cert?` on a `QQ` goal whose cofactors are not integral prints a `/ d`.
These are those lines, unedited.  The kernel checks `d * (p - r) = Σ qᵢ' gᵢ`
over the integers and `Rat`'s `Macaulean.CASRingRat` instance cancels the `d`.
-/

theorem paste_scaled (x y z : Rat) (h1 : 3 * x * y - 3 * z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  poly_cert ["2.0.0.1 0.0.1.1", "0.0.0.0"] / 3 in [x, y, z] using [h1, h2]

theorem paste_scaled_lcm (x y z : Rat)
    (h1 : 3 * (x * y - z) = 0) (h2 : 2 * (y ^ 2 - x) = 0) :
    x * y - z + y ^ 2 - x = 0 := by
  poly_cert ["0.0.0.2", "0.0.0.3"] / 6 in [x, y, z] using [h1, h2]

/-- A scaled cofactor may be an ordinary term too. -/
theorem term_scaled (x y z : Rat) (h1 : 3 * x * y - 3 * z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  poly_cert [x ^ 2 + z, 0] / 3 using [h1, h2]

/-! ## Scaled divisibility

Lean core gives `Rat` no `Dvd`; this is the instance every `CommMonoid` has in
Mathlib (`semigroupDvd`), spelled out.  It is also the check that `poly_cert`
needs no `Dvd` field in `CASRing`: the tactic unfolds the goal with `whnf`,
and an instance of this shape *is* the `∃` definitionally.
-/

local instance : Dvd Rat := ⟨fun a b => ∃ c, b = a * c⟩

/-- `x - y + z = (2x - 2y + 2z) * (1/2)`: the witness itself is not integral,
which plain cancellation could not produce -- `CASRingRat.dvd_witness` does. -/
theorem dvd_scaled (x y z : Rat) : (2 * x - 2 * y + 2 * z) ∣ (x - y + z) := by
  poly_cert ["0.0.0.1"] / 2 in [x, y, z]

/-! ## Cofactors as terms

A monomial string and the term it stands for produce the same proof, so a
certificate may equally well be a named constant.
-/

theorem term_dvd (x y z : Int) :
    (x ^ 2 * y - z + 1) ∣ ((x ^ 2 * y - z + 1) * (x * y + 2 * z - 3)) := by
  poly_cert [x * y + 2 * z - 3]

theorem term_mem (x y z : Rat) (h1 : x * y - z = 0) (h2 : y ^ 2 - x = 0) :
    x ^ 3 * y + x * y * z + 5 = x ^ 2 * z + z ^ 2 + 5 := by
  poly_cert [x ^ 2 + z, 0] using [h1, h2]

/-! ## `poly_def` data feeding `poly_cert`

When the ring's variables are *constants* rather than the goal's bound
variables, the same monomial strings go into `poly_def` and the resulting
constant into `poly_cert`.  Here the "variables" are the `Int` terms `2`, `3`
and `5`, the way `MacauleanTest/PolyDef.lean` does it.
-/

/-- `2 * 3 + 2 * 5 - 3`, i.e. the cofactor `x*y + 2*z - 3` at `x, y, z = 2, 3, 5`. -/
poly_def quot_data : Int in [2, 3, 5] := "1.1.0.1 0.0.1.2 0.0.0.-3"

-- (one atom, so the tactic's small-`Nat` key advisory fires; it is about speed,
-- not correctness)
#guard_msgs(drop warning) in
theorem def_dvd : ((2:Int) ^ 2 * 3 - 5 + 1) ∣ (((2:Int) ^ 2 * 3 - 5 + 1) * quot_data) := by
  poly_cert [quot_data]

/-! ## Axioms -/

/-- info: 'MacauleanTest.PolyCert.paste_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paste_dvd

/-- info: 'MacauleanTest.PolyCert.paste_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paste_mem

/-- info: 'MacauleanTest.PolyCert.def_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms def_dvd

/-- info: 'MacauleanTest.PolyCert.paste_scaled_lcm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paste_scaled_lcm

/-- info: 'MacauleanTest.PolyCert.dvd_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_scaled

/--
info: 'MacauleanTest.PolyCert.paste_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 paste_native._native.decide.ax_1_1]
-/
#guard_msgs in
#print axioms paste_native

/-! ## Misuse -/

-- A monomial string needs the variables spelled out.
/-- error: poly_cert: a monomial-string cofactor has to say which variables it is written in; add `in [x, y, …]` -/
#guard_msgs in
example (x y z : Int) :
    (x ^ 2 * y - z + 1) ∣ ((x ^ 2 * y - z + 1) * (x * y + 2 * z - 3)) := by
  poly_cert ["1.1.0.1 0.0.1.2 0.0.0.-3"]

-- Scaling has to be cancellable, and `Int` cannot cancel a 2.  The message
-- names the class rather than reporting a failed check.
/--
error: poly_cert: this certificate is scaled by 2, which needs to be cancelled at the end, but
  Int
has no `Macaulean.CASRingRat` instance.  Either give it one (see `Macaulean/CASRing.lean`) or supply integral cofactors.
-/
#guard_msgs in
example (x y z : Int) (h : 2 * x - 2 * y + 2 * z = 0) : x = y - z := by
  poly_cert ["0.0.0.1"] / 2 in [x, y, z] using [h]

-- A wrong scale factor is rejected like any other wrong certificate.
example (x y z : Rat) (h : 2 * x - 2 * y + 2 * z = 0) : x = y - z := by
  fail_if_success poly_cert ["0.0.0.1"] / 3 in [x, y, z] using [h]
  poly_cert ["0.0.0.1"] / 2 in [x, y, z] using [h]

/-! ## The instances this library ships -/

/-- info: Macaulean.instCASRingInt -/
#guard_msgs in
#synth Macaulean.CASRing Int

/-- info: Macaulean.instCASRingRatRat -/
#guard_msgs in
#synth Macaulean.CASRingRat Rat

/-- info: Macaulean.instCASRingRatRat.toCASRing -/
#guard_msgs in
#synth Macaulean.CASRing Rat

-- `CASRing.toCommRing` sits at priority 100, so a ring's own
-- `Grind.CommRing` instance is still the one that gets found: nothing
-- downstream sees a new instance path just because this class exists.
/-- info: Lean.Grind.instFieldRat.toCommRing -/
#guard_msgs in
#synth Lean.Grind.CommRing Rat

/-- info: Lean.Grind.instCommRingInt -/
#guard_msgs in
#synth Lean.Grind.CommRing Int

/-! ## Misuse (continued) -/

/-- A wrong cofactor fails the reflective check rather than being believed. -/
example (x y z : Int) :
    (x ^ 2 * y - z + 1) ∣ ((x ^ 2 * y - z + 1) * (x * y + 2 * z - 3)) := by
  fail_if_success poly_cert [x * y + 2 * z]
  poly_cert [x * y + 2 * z - 3]

end MacauleanTest.PolyCert
