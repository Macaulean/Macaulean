import Macaulean.Verification.Views

/-!
Typed finitely generated ideal presentations. Membership is coefficientwise
polynomial combination, not equality of evaluations or sparse representations.
The presentation retains the runtime ring identity. Different presentations may
describe the same ideal; `SameIdeal` expresses equality of their membership sets.
-/
namespace Macaulean.M2.Verification.Views
open Polynomials

structure IdealPresentation (ring : RingInfo) where
  generators : List (Polynomial ring)

def IdealPresentation.Member (I : IdealPresentation r) (p : Polynomial r) : Prop :=
  ∃ row : Row r I.generators.length, Represents p I.generators row

def IdealPresentation.SameIdeal (I J : IdealPresentation r) : Prop :=
  ∀ p, I.Member p ↔ J.Member p

def IdealPresentation.value (I : IdealPresentation r) : Value :=
  .algebra (.ideal r (I.generators.map Polynomial.raw))

def readIdeal (r : RingInfo) : Value → Except String (IdealPresentation r)
  | .algebra (.ideal s generators) =>
    if r = s then
      IdealPresentation.mk <$> readPolynomials r
        (generators.map fun raw => .algebra (.poly r raw))
    else .error "ideal view: foreign ring identity"
  | _ => .error "ideal view: expected an ideal"

theorem polynomials_roundtrip (ps : List (Polynomial r)) :
    readPolynomials r (ps.map Polynomial.value) = .ok ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [readPolynomials, polynomial_roundtrip, ih, bind, Except.bind,
      pure, Except.pure]

theorem ideal_roundtrip (I : IdealPresentation r) :
    readIdeal r I.value = .ok I := by
  cases I with
  | mk gs =>
    simp only [readIdeal, IdealPresentation.value, List.map_map]
    change IdealPresentation.mk <$> readPolynomials r (gs.map Polynomial.value) = _
    rw [polynomials_roundtrip]
    rfl

theorem ideal_foreign_ring (r s : RingInfo) (gs : List Raw) (h : r ≠ s) :
    readIdeal r (.algebra (.ideal s gs)) = .error "ideal view: foreign ring identity" := by
  simp [readIdeal, h]

theorem IdealPresentation.member_equivalent (I : IdealPresentation r)
    (p q : Polynomial r) (h : Equivalent p q) : I.Member p ↔ I.Member q := by
  constructor
  · rintro ⟨row, hr⟩
    exact ⟨row, fun powers => (h powers).symm.trans (hr powers)⟩
  · rintro ⟨row, hr⟩
    exact ⟨row, fun powers => (h powers).trans (hr powers)⟩

theorem IdealPresentation.sameIdeal_refl (I : IdealPresentation r) : I.SameIdeal I :=
  fun _ => Iff.rfl

theorem IdealPresentation.sameIdeal_symm (I J : IdealPresentation r)
    (h : I.SameIdeal J) : J.SameIdeal I := fun p => (h p).symm

theorem IdealPresentation.sameIdeal_trans (I J K : IdealPresentation r)
    (h : I.SameIdeal J) (k : J.SameIdeal K) : I.SameIdeal K :=
  fun p => (h p).trans (k p)

end Macaulean.M2.Verification.Views
