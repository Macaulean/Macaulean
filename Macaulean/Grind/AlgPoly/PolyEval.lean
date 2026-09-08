/-
  Evaluating a reified `AlgExpr Int` into `Macaulean.Polynomial Int nv`, and the
  soundness theorem the tactic closes goals with.

  Everything here is written so that the *kernel* can run it: `toPoly` is
  structural, and every polynomial operation it calls bottoms out in
  `mergeTermsF`, which is fuel-indexed structural recursion.  In particular
  nothing on this path ever calls `sortTerms` (`List.mergeSort` is well-founded
  and the kernel cannot unfold it).
-/
import Macaulean.Grind.AlgPoly.Expr

namespace Macaulean

open Lean Grind CommRing

namespace AlgExpr

/--
Evaluate a reified expression to a polynomial in `nv` variables.

`none` means the expression mentions a variable index `≥ nv`, which the tactic
never produces; making it explicit keeps `toPoly` total.
-/
def toPoly (nv : Nat) : AlgExpr Int → Option (Polynomial Int nv)
  | .coeff k => some ⟨Polynomial.removeZeros [⟨k, Mon.unit⟩]⟩
  | .var i => if h : i < nv then some (Polynomial.ofVar ⟨i, h⟩) else none
  | .add a b =>
    match toPoly nv a, toPoly nv b with
    | some p, some q => some (p.add q)
    | _, _ => none
  | .sub a b =>
    match toPoly nv a, toPoly nv b with
    | some p, some q => some (p.sub q)
    | _, _ => none
  | .mul a b =>
    match toPoly nv a, toPoly nv b with
    | some p, some q => some (p.mul q)
    | _, _ => none
  | .neg a => (toPoly nv a).map Polynomial.neg
  | .pow a k => (toPoly nv a).map (Polynomial.pow · k)

/-- The certificate the kernel checks: both sides evaluate, and to the same
normal form. -/
def checkPolyEq (nv : Nat) (e₁ e₂ : AlgExpr Int) : Bool :=
  match toPoly nv e₁, toPoly nv e₂ with
  | some p, some q => p == q
  | _, _ => false

section

variable {A : Type} [Grind.CommRing A] {φ : Int → A}
  (hφ : Polynomial.IsCoeffHom φ) (ctx : Context A)

include hφ

/-- Evaluating to a polynomial preserves the denotation. -/
theorem denote_toPoly (nv : Nat) :
    ∀ (e : AlgExpr Int) (p : Polynomial Int nv), toPoly nv e = some p →
      Polynomial.denoteWith φ ctx p = e.denote φ ctx := by
  intro e
  induction e with
  | coeff k =>
    intro p hp
    cases hp
    show Polynomial.denoteTerms ctx
      (Polynomial.mapCoeffTerms φ (Polynomial.removeZeros [⟨k, Mon.unit⟩])) = φ k
    rw [Polynomial.denoteTerms_mapCoeffTerms_removeZeros hφ]
    exact Polynomial.denoteWith_ofConst hφ ctx k
  | var i =>
    intro p hp
    by_cases h : i < nv
    · simp only [toPoly, h, dif_pos, Option.some.injEq] at hp
      subst hp
      exact Polynomial.denoteWith_ofVar hφ ctx ⟨i, h⟩
    · simp [toPoly, h] at hp
  | add a b iha ihb =>
    intro p hp
    simp only [toPoly] at hp
    split at hp
    · rename_i pa pb ha hb
      cases hp
      rw [Polynomial.denoteWith_add hφ, iha _ ha, ihb _ hb]; rfl
    · exact absurd hp (by simp)
  | sub a b iha ihb =>
    intro p hp
    simp only [toPoly] at hp
    split at hp
    · rename_i pa pb ha hb
      cases hp
      rw [Polynomial.denoteWith_sub hφ, iha _ ha, ihb _ hb]; rfl
    · exact absurd hp (by simp)
  | mul a b iha ihb =>
    intro p hp
    simp only [toPoly] at hp
    split at hp
    · rename_i pa pb ha hb
      cases hp
      rw [Polynomial.denoteWith_mul hφ, iha _ ha, ihb _ hb]; rfl
    · exact absurd hp (by simp)
  | neg a iha =>
    intro p hp
    simp only [toPoly, Option.map_eq_some_iff] at hp
    obtain ⟨pa, ha, rfl⟩ := hp
    rw [Polynomial.denoteWith_neg hφ, iha _ ha]; rfl
  | pow a k iha =>
    intro p hp
    simp only [toPoly, Option.map_eq_some_iff] at hp
    obtain ⟨pa, ha, rfl⟩ := hp
    rw [Polynomial.denoteWith_pow hφ, iha _ ha]; rfl

/--
**Soundness of the reflective check.**

If both sides evaluate to the *same* `Polynomial Int nv`, they denote the same
element of `A`.

Only this direction is needed, and it needs nothing but `LawfulBEq`: equal
normal forms give equal denotations.  Whether equal expressions *do* reach equal
normal forms is completeness, and that is what the sortedness invariant is for
(`Polynomial.sorted_add`, `Polynomial.sorted_mul`): `add` and `mul` both merge
grevlex-descending term lists, coalescing equal monomials, and then strip zero
coefficients, so on sorted inputs they produce the unique sorted zero-free
normal form and a plain `BEq` is decisive.  Nothing here relies on that.
-/
theorem eq_of_checkPolyEq (nv : Nat) (e₁ e₂ : AlgExpr Int)
    (h : checkPolyEq nv e₁ e₂ = true) :
    e₁.denote φ ctx = e₂.denote φ ctx := by
  unfold checkPolyEq at h
  split at h
  · rename_i p q hp hq
    rw [← denote_toPoly hφ ctx nv e₁ p hp, ← denote_toPoly hφ ctx nv e₂ q hq,
      eq_of_beq h]
  · exact absurd h (by simp)

end

end AlgExpr

end Macaulean
