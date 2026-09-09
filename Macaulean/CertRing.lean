/-
Copyright (c) 2026 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Macaulean.Polynomial.Hom

@[expose] public section

/-!
# `CertRing`: one instance to subscribe a ring to the certificate machinery

`algebra_norm_reflect`, `poly_cert` and `m2cert` all do their arithmetic in
`Macaulean.Polynomial Int nv` -- the kernel can compute there, and only there,
on the small-`Nat` fast path -- and denote the result back into the ring the
goal is stated in.  Everything ring-specific that those tactics need is
collected here, so a consumer ring declares *one* instance and every tactic in
the library works on its goals.

`CertRing R` bundles:

* `ofInt : Int → R`, the coefficient map, with its `IsCoeffHom` proof.  The
  kernel carrier stays `Int` on purpose: `Rat` arithmetic goes through
  `Nat.gcd`, which is an out-of-line GMP call and falls off the kernel's
  small-`Nat` fast path.
* the `Lean.Grind.CommRing R` structure itself (as the parent), so
  `[CertRing R]` alone meets the reflective layer's instance needs;
* `m2BaseRing`, the Macaulay2 base ring the coefficients are serialised into.

What it deliberately does *not* bundle:

* **variables/atoms.**  `Macaulean.AlgPoly.Reify` treats anything it does not
  recognise as arithmetic as an atom, up to definitional equality, so
  `MvPolynomial.X i` and `Polynomial.X` need no help: they simply become
  variables of the reified expression.  There is no hook because no code would
  call it.
* **`Dvd`.**  `poly_cert` unfolds a goal `g ∣ f` with `whnf`.  Both the
  instances Lean core gives commutative rings and Mathlib's `semigroupDvd` are
  literally `⟨fun a b => ∃ c, b = a * c⟩`, so the unfolding is definitional and
  a class field would only restate it.

`CertRingRat R` is the optional extension for rings that admit `1/d` for a
nonzero integer `d`.  It is what lets the tactics accept the *non-integral*
cofactors Macaulay2 returns over `QQ`: scale by the least common denominator
`d`, check the integer identity `d * (p - r) = Σ qᵢ' gᵢ` reflectively, and
cancel `d` at the end (`CertRingRat.cancel`, `CertRingRat.dvd_witness`).  Rings
that only ever see integer cofactors need not provide it.
-/

namespace Macaulean

open Lean Grind

/-! ### The canonical coefficient map `Int → A` -/

/--
The canonical coefficient map `Int → A`.

`Lean.Grind.CommRing.denoteInt` is grind's own canonical map: it produces
`OfNat.ofNat |k|` (negated when `k < 0`) through grind's numeral instance, which
is exactly what makes the tactic's denotation bridge reduce to the goal's own
numerals.  Packaging it as a named definition keeps the `Grind.Ring` instance
argument in one place, so the term the tactic emits and the term
`intDenote_isCoeffHom` talks about are syntactically identical.

This is the `ofInt` of every `CertRing` instance in this library, and the
default one `CertRing.ofGrindCommRing` gives a ring that has not subscribed.
-/
noncomputable def intDenote (A : Type) [Grind.CommRing A] : Int → A :=
  fun k => Grind.CommRing.denoteInt k

theorem intDenote_isCoeffHom (A : Type) [Grind.CommRing A] :
    Polynomial.IsCoeffHom (intDenote A) where
  map_zero := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_zero
  map_one := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_one
  map_add a b := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_add a b
  map_mul a b := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_mul a b
  map_neg a := by
    simp only [intDenote, Grind.CommRing.denoteInt_eq]
    exact Grind.Ring.intCast_neg a

/-! ### The Macaulay2 base ring -/

/--
The base ring a certificate's coefficients are serialised into when the request
goes to Macaulay2.  `ZZ` promises integral cofactors; `QQ` allows Macaulay2 to
divide, and then the tactics take the scaling path (see `CertRingRat`).
-/
inductive M2BaseRing where
  /-- The integers. -/
  | ZZ
  /-- The rationals. -/
  | QQ
  deriving DecidableEq, Repr, Inhabited

/-- Macaulay2's own spelling. -/
def M2BaseRing.toString : M2BaseRing → String
  | .ZZ => "ZZ"
  | .QQ => "QQ"

instance : ToString M2BaseRing := ⟨M2BaseRing.toString⟩

/-! ### `CertRing` -/

/--
A commutative ring that has subscribed to the certificate machinery.

Declare one instance and `algebra_norm_reflect`, `poly_cert`, `m2cert` and
`m2cert?` all work on goals stated over `R`.  A ring with no instance still
gets the reflective identity check: the tactics fall back on
`CertRing.ofGrindCommRing R` (base ring `ZZ`, `ofInt = intDenote R`), which is
what they hard-wired before this class existed.

The class *extends* `Lean.Grind.CommRing R`, so `[CertRing R]` on its own is
enough to state and prove everything the reflective layer needs.  The parent
projection is registered at priority 100 so that a concrete ring's own
`Grind.CommRing` instance still wins.
-/
class CertRing (R : Type) extends Lean.Grind.CommRing R where
  /-- The coefficient map.  The kernel works over `Int`; this is how its
  coefficients reach `R`. -/
  ofInt : Int → R
  /-- `ofInt` is a ring map on the nose -- which pins it down: any two maps
  satisfying this agree. -/
  ofInt_isCoeffHom : Polynomial.IsCoeffHom ofInt
  /-- The Macaulay2 base ring to serialise coefficients into. -/
  m2BaseRing : M2BaseRing

attribute [instance 100] CertRing.toCommRing

/--
The default subscription for any `Lean.Grind.CommRing`: coefficients travel
through `intDenote`, and the Macaulay2 base ring is `ZZ` unless said otherwise.

A consumer whose ring wants nothing special writes

```lean
noncomputable instance : Macaulean.CertRing MyRing :=
  Macaulean.CertRing.ofGrindCommRing MyRing
```

This is a `def` rather than an `instance` on purpose: a generic
`[Grind.CommRing R] → CertRing R` instance and the `CertRing.toCommRing`
projection instance close a synthesis loop, and priority games around it are
not worth the fragility.
-/
@[instance_reducible]
noncomputable def CertRing.ofGrindCommRing (R : Type) [inst : Lean.Grind.CommRing R]
    (base : M2BaseRing := .ZZ) : CertRing R where
  toCommRing := inst
  ofInt := intDenote R
  ofInt_isCoeffHom := intDenote_isCoeffHom R
  m2BaseRing := base

/-! ### `CertRingRat`: rings that can cancel an integer denominator -/

/--
A `CertRing` in which every nonzero integer is invertible.

Macaulay2 working over `QQ` routinely returns cofactors with denominators, and
`Rat` has no place in the kernel certificate (its arithmetic goes through
`Nat.gcd`, an out-of-line GMP call).  The way out is to scale: multiply the
whole certificate by the least common denominator `d`, check the *integer*
identity in the kernel, and undo the scaling with `invOfInt d` afterwards.
That last step is the only thing this class adds.

`invOfInt` is a plain function rather than an `Inv R`: the rings that need it
are typically not fields (`MvPolynomial (Fin 3) ℚ` is the motivating one), they
merely contain `ℚ`.
-/
class CertRingRat (R : Type) extends CertRing R where
  /-- A right inverse for `ofInt d`, for `d ≠ 0`. -/
  invOfInt : Int → R
  /-- …which is what makes it one. -/
  mul_invOfInt : ∀ d : Int, d ≠ 0 → CertRing.ofInt d * invOfInt d = 1

namespace CertRingRat

variable {R : Type} [CertRingRat R]

/--
**Cancellation.**  This is what turns the scaled, integer-coefficient identity
the kernel checked back into the identity that was asked for.
-/
theorem cancel (d : Int) (hd : d ≠ 0) (a b : R)
    (h : CertRing.ofInt d * a = CertRing.ofInt d * b) : a = b := by
  have h1 := CertRingRat.mul_invOfInt (R := R) d hd
  calc a = (CertRing.ofInt d * invOfInt d) * a := by rw [h1, Semiring.one_mul]
    _ = invOfInt d * (CertRing.ofInt d * a) := by
          rw [CommSemiring.mul_comm (CertRing.ofInt d) (invOfInt d), Semiring.mul_assoc]
    _ = invOfInt d * (CertRing.ofInt d * b) := by rw [h]
    _ = (CertRing.ofInt d * invOfInt d) * b := by
          rw [CommSemiring.mul_comm (CertRing.ofInt d) (invOfInt d), Semiring.mul_assoc]
    _ = b := by rw [h1, Semiring.one_mul]

/--
**The divisibility witness.**  Macaulay2's scaled certificate `d * f = g * q'`
gives the unscaled witness `q'/d` directly, which is what `g ∣ f` wants.
-/
theorem dvd_witness (d : Int) (hd : d ≠ 0) (f g q : R)
    (h : CertRing.ofInt d * f = g * q) : f = g * (invOfInt d * q) := by
  have h1 := CertRingRat.mul_invOfInt (R := R) d hd
  calc f = (CertRing.ofInt d * invOfInt d) * f := by rw [h1, Semiring.one_mul]
    _ = invOfInt d * (CertRing.ofInt d * f) := by
          rw [CommSemiring.mul_comm (CertRing.ofInt d) (invOfInt d), Semiring.mul_assoc]
    _ = invOfInt d * (g * q) := by rw [h]
    _ = g * (invOfInt d * q) := by
          rw [← Semiring.mul_assoc, CommSemiring.mul_comm (invOfInt d) g, Semiring.mul_assoc]

end CertRingRat

/--
Every `Lean.Grind.Field` of characteristic zero is a `CertRingRat`, with
`invOfInt d = (ofInt d)⁻¹`.  This is how the `Rat` instance below is built, and
it is the right helper for a consumer working in an honest field.  A ring that
merely *contains* `ℚ` -- `MvPolynomial (Fin 3) ℚ`, a function field's
polynomial ring -- writes the instance by hand instead (see the doc comment on
`CertRing`'s `MvPolynomial` example in `docs/poly-repr-reflect.md`).
-/
@[instance_reducible]
noncomputable def CertRingRat.ofGrindField (R : Type) [inst : Lean.Grind.Field R]
    [Lean.Grind.IsCharP R 0] : CertRingRat R where
  toCertRing := CertRing.ofGrindCommRing R .QQ
  invOfInt d := (intDenote R d)⁻¹
  mul_invOfInt d hd :=
    Lean.Grind.CommRing.inv_int_eq (α := R) d (by simp [hd])

/-! ### The instances this library ships -/

/-- `Int` certifies over `ZZ`, with integral cofactors and no scaling. -/
noncomputable instance : CertRing Int := CertRing.ofGrindCommRing Int .ZZ

/-- `Rat` certifies over `QQ`; a non-integral cofactor is scaled away and the
denominator cancelled. -/
noncomputable instance : CertRingRat Rat := CertRingRat.ofGrindField Rat

end Macaulean

end
