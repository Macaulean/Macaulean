/-
  Denoting a `Polynomial C n` in a *different* ring `A`, through a ring
  morphism on the coefficients.

  This is what lets a reflective tactic do all its arithmetic in
  `Polynomial Int n` -- where the kernel can actually compute -- while the goal
  it closes lives in an arbitrary `Lean.Grind.CommRing A`.
-/
import Macaulean.Polynomial.Lemmas

open Lean Grind CommRing

namespace Macaulean

set_option linter.unusedSectionVars false

namespace Polynomial

/--
The (minimal) hypotheses on a coefficient map `φ : C → A` needed by the
denotation lemmas below.  Deliberately a bare structure rather than a class:
the tactic supplies the single instance it needs (`Int.cast`) explicitly.
-/
structure IsCoeffHom {C A : Type} [Grind.CommRing C] [Grind.CommRing A] (φ : C → A) : Prop where
  map_zero : φ 0 = 0
  map_one : φ 1 = 1
  map_add : ∀ a b, φ (a + b) = φ a + φ b
  map_mul : ∀ a b, φ (a * b) = φ a * φ b
  map_neg : ∀ a, φ (-a) = -φ a

section

variable {C A : Type} {n : Nat} [Grind.CommRing C] [Grind.CommRing A]

/-- Push a coefficient map through a term list. -/
def mapCoeffTerms (φ : C → A) (ts : List (PolyTerm C n)) : List (PolyTerm A n) :=
  ts.map fun t => ⟨φ t.coefficient, t.monomial⟩

/-- Push a coefficient map through a polynomial. -/
def mapCoeff (φ : C → A) (p : Polynomial C n) : Polynomial A n :=
  ⟨mapCoeffTerms φ p.terms⟩

/-- Denote a `Polynomial C n` in `A`, mapping coefficients by `φ`. -/
def denoteWith (φ : C → A) (ctx : Context A) (p : Polynomial C n) : A :=
  denoteTerms ctx (mapCoeffTerms φ p.terms)

@[simp]
theorem mapCoeffTerms_nil (φ : C → A) : mapCoeffTerms (n := n) φ [] = [] := rfl

@[simp]
theorem mapCoeffTerms_cons (φ : C → A) (t : PolyTerm C n) (ts : List (PolyTerm C n)) :
    mapCoeffTerms φ (t :: ts) = ⟨φ t.coefficient, t.monomial⟩ :: mapCoeffTerms φ ts := rfl

@[simp]
theorem denoteWith_mk (φ : C → A) (ctx : Context A) (ts : List (PolyTerm C n)) :
    denoteWith φ ctx ⟨ts⟩ = denoteTerms ctx (mapCoeffTerms φ ts) := rfl

/-! ### `mapCoeffTerms` is a homomorphism for the list-level operations -/

theorem mapCoeffTerms_mergeTerms {φ : C → A} (hφ : IsCoeffHom φ)
    (xs ys : List (PolyTerm C n)) :
    mapCoeffTerms φ (mergeTerms xs ys) =
      mergeTerms (mapCoeffTerms φ xs) (mapCoeffTerms φ ys) := by
  induction xs generalizing ys
  case nil => simp
  case cons x xs ih =>
    induction ys
    case nil => simp
    case cons y ys ih2 =>
      rw [mergeTerms_cons_cons, mapCoeffTerms_cons, mapCoeffTerms_cons,
        mergeTerms_cons_cons]
      cases h : x.monomial.grevlex y.monomial <;> simp only [mapCoeffTerms_cons]
      · exact congrArg _ ih2
      · rw [hφ.map_add]; exact congrArg _ (ih ys)
      · exact congrArg _ (ih (y :: ys))

theorem mapCoeffTerms_mulMonTerms {φ : C → A} (hφ : IsCoeffHom φ)
    (c : C) (m : Mon n) (ts : List (PolyTerm C n)) :
    mapCoeffTerms φ (mulMonTerms c m ts) = mulMonTerms (φ c) m (mapCoeffTerms φ ts) := by
  simp [mapCoeffTerms, mulMonTerms, List.map_map, Function.comp_def, hφ.map_mul]

theorem mapCoeffTerms_mulTerms {φ : C → A} (hφ : IsCoeffHom φ)
    (xs ys : List (PolyTerm C n)) :
    mapCoeffTerms φ (mulTerms xs ys) =
      mulTerms (mapCoeffTerms φ xs) (mapCoeffTerms φ ys) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [mulTerms_cons_cons, mapCoeffTerms_cons, mapCoeffTerms_cons, mapCoeffTerms_cons,
        mulTerms_cons_cons, mapCoeffTerms_mergeTerms hφ, mapCoeffTerms_mulMonTerms hφ,
        ih (y :: ys), hφ.map_mul]
      rfl

theorem mapCoeffTerms_neg {φ : C → A} (hφ : IsCoeffHom φ) (ts : List (PolyTerm C n)) :
    mapCoeffTerms φ (ts.map fun t => ⟨-t.coefficient, t.monomial⟩) =
      (mapCoeffTerms φ ts).map fun t => ⟨-t.coefficient, t.monomial⟩ := by
  simp [mapCoeffTerms, List.map_map, Function.comp_def, hφ.map_neg]

/-- `removeZeros` drops terms whose coefficient is zero in `C`; `φ 0 = 0`, so
this does not change the denotation in `A`.  (The converse -- a coefficient that
becomes zero only in `A` -- is not needed, and is not true in general.) -/
theorem denoteTerms_mapCoeffTerms_removeZeros [BEq C] [LawfulBEq C]
    {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A) (ts : List (PolyTerm C n)) :
    denoteTerms ctx (mapCoeffTerms φ (removeZeros ts)) =
      denoteTerms ctx (mapCoeffTerms φ ts) := by
  induction ts with
  | nil => simp [removeZeros]
  | cons t ts ih =>
    by_cases h : t.coefficient = 0
    · rw [removeZeros_cons_zero t ts h, ih, mapCoeffTerms_cons, denoteTerms_cons, h,
        hφ.map_zero, Semiring.zero_mul, AddCommMonoid.zero_add]
    · rw [removeZeros_cons_nonzero t ts h, mapCoeffTerms_cons, mapCoeffTerms_cons,
        denoteTerms_cons, denoteTerms_cons, ih]

/-! ### The denotation lemmas -/

variable [BEq C] [LawfulBEq C]

theorem denoteWith_add {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A)
    (p q : Polynomial C n) :
    denoteWith φ ctx (p.add q) = denoteWith φ ctx p + denoteWith φ ctx q := by
  show denoteTerms ctx (mapCoeffTerms φ (removeZeros (mergeTerms p.terms q.terms))) = _
  rw [denoteTerms_mapCoeffTerms_removeZeros hφ, mapCoeffTerms_mergeTerms hφ,
    denoteTerms_mergeTerms]
  rfl

theorem denoteWith_neg {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A)
    (p : Polynomial C n) :
    denoteWith φ ctx p.neg = -denoteWith φ ctx p := by
  show denoteTerms ctx (mapCoeffTerms φ (p.terms.map fun t => ⟨-t.coefficient, t.monomial⟩)) = _
  rw [mapCoeffTerms_neg hφ]
  exact denote_neg (R := A) ctx ⟨mapCoeffTerms φ p.terms⟩

theorem denoteWith_sub {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A)
    (p q : Polynomial C n) :
    denoteWith φ ctx (p.sub q) = denoteWith φ ctx p - denoteWith φ ctx q := by
  rw [Polynomial.sub, denoteWith_add hφ, denoteWith_neg hφ, Ring.sub_eq_add_neg]

theorem denoteWith_mul {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A)
    (p q : Polynomial C n) :
    denoteWith φ ctx (p.mul q) = denoteWith φ ctx p * denoteWith φ ctx q := by
  show denoteTerms ctx (mapCoeffTerms φ (removeZeros (mulTerms p.terms q.terms))) = _
  rw [denoteTerms_mapCoeffTerms_removeZeros hφ, mapCoeffTerms_mulTerms hφ,
    denoteTerms_mulTerms]
  rfl

theorem denoteWith_one {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A) :
    denoteWith φ ctx (⟨[⟨1, Mon.unit⟩]⟩ : Polynomial C n) = 1 := by
  show φ 1 * Mon.unit.denote ctx + denoteTerms ctx [] = 1
  rw [hφ.map_one, Mon.denote_unit, Semiring.mul_one, denoteTerms_nil, Semiring.add_zero]

theorem denoteWith_pow {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A)
    (p : Polynomial C n) (k : Nat) :
    denoteWith φ ctx (p.pow k) = denoteWith φ ctx p ^ k := by
  induction k with
  | zero => rw [Semiring.pow_zero]; exact denoteWith_one hφ ctx
  | succ k ih =>
    rw [Polynomial.pow, denoteWith_mul hφ, ih, Semiring.pow_succ,
      CommSemiring.mul_comm]

theorem denoteWith_ofVar {φ : C → A} (hφ : IsCoeffHom φ) (ctx : Context A) (i : Fin n) :
    denoteWith φ ctx (ofVar i) = ctx.get i := by
  show φ 1 * (Mon.fromVar i).denote ctx + denoteTerms ctx [] = _
  rw [hφ.map_one, Mon.denote_fromVar, Semiring.one_mul, denoteTerms_nil,
    Semiring.add_zero]
  rfl

theorem denoteWith_ofConst {φ : C → A} (_hφ : IsCoeffHom φ) (ctx : Context A) (c : C) :
    denoteWith φ ctx (ofConst (n := n) c) = φ c := by
  show φ c * Mon.unit.denote ctx + denoteTerms ctx [] = _
  rw [Mon.denote_unit, Semiring.mul_one, denoteTerms_nil, Semiring.add_zero]

/-- Equal normal forms denote equally.  This is the only direction soundness
needs; it says nothing about whether equal polynomials *have* equal normal
forms (that is completeness, and it is what sortedness is for). -/
theorem denoteWith_congr {φ : C → A} (ctx : Context A) {p q : Polynomial C n}
    (h : (p == q) = true) : denoteWith φ ctx p = denoteWith φ ctx q := by
  rw [eq_of_beq h]

end

end Polynomial

end Macaulean
