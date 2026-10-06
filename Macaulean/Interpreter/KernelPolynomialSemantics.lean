import Macaulean.Interpreter.KernelPolynomial
import Macaulean.Polynomial.Lemmas
import Init.GrindInstances.Ring.Rat

/-!
Semantic laws for the polynomial arithmetic actually used by the M2 interpreter.
Inputs need not be sorted, normalized, or free of duplicate/zero terms. These
laws concern arbitrary polynomials, not evaluation of a fixed source example.
-/
namespace Macaulean.M2.KernelPolynomial
open Macaulean Polynomial Lean.Grind

theorem denoteTerms_insert (ctx : Lean.Grind.CommRing.Context Rat) (t : PolyTerm Rat n)
    (ts : List (PolyTerm Rat n)) :
    Polynomial.denoteTerms ctx (insert t ts) =
      t.coefficient * t.monomial.denote ctx + Polynomial.denoteTerms ctx ts := by
  induction ts with
  | nil =>
    simp only [insert]
    split <;> simp_all [Polynomial.denoteTerms] <;> grind
  | cons u us ih =>
    simp only [insert]
    split
    · split <;> simp_all [Polynomial.denoteTerms] <;> grind
    · next h =>
        have hm : t.monomial = u.monomial :=
          Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex) h
        split <;> simp_all [Polynomial.denoteTerms] <;> grind
    · simp only [Polynomial.denoteTerms_cons, ih]
      grind

private theorem denoteTerms_fold_insert (ctx : Lean.Grind.CommRing.Context Rat)
    (ts acc : List (PolyTerm Rat n)) :
    Polynomial.denoteTerms ctx (ts.foldl (fun xs t => insert t xs) acc) =
      Polynomial.denoteTerms ctx acc + Polynomial.denoteTerms ctx ts := by
  induction ts generalizing acc with
  | nil => simp [Polynomial.denoteTerms] <;> grind
  | cons t ts ih =>
    simp only [List.foldl_cons, ih, denoteTerms_insert, Polynomial.denoteTerms_cons]
    grind

theorem denote_normalize (ctx : Lean.Grind.CommRing.Context Rat) (p : Polynomial Rat n) :
    (normalize p).denote ctx = p.denote ctx := by
  simp [normalize, Polynomial.denote, denoteTerms_fold_insert]
  grind

theorem denote_add (ctx : Lean.Grind.CommRing.Context Rat) (p q : Polynomial Rat n) :
    (add p q).denote ctx = p.denote ctx + q.denote ctx := by
  rw [add, denote_normalize]
  exact Polynomial.denoteTerms_append ctx p.terms q.terms

theorem denote_sub (ctx : Lean.Grind.CommRing.Context Rat) (p q : Polynomial Rat n) :
    (sub p q).denote ctx = p.denote ctx - q.denote ctx := by
  rw [sub, denote_add]
  have hn : q.neg.denote ctx = -q.denote ctx := by
    rcases q with ⟨ts⟩
    simp only [Polynomial.neg, Polynomial.denote]
    induction ts with
    | nil => simp [Polynomial.denoteTerms] <;> grind
    | cons t ts ih =>
      simp only [List.map_cons, Polynomial.denoteTerms_cons, ih]
      grind
  rw [hn]
  grind

private theorem denoteTerms_products (ctx : Lean.Grind.CommRing.Context Rat)
    (ps qs : List (PolyTerm Rat n)) :
    Polynomial.denoteTerms ctx
      (ps.flatMap fun t => Polynomial.mulMonTerms t.coefficient t.monomial qs) =
      Polynomial.denoteTerms ctx ps * Polynomial.denoteTerms ctx qs := by
  induction ps with
  | nil => simp [Polynomial.denoteTerms] <;> grind
  | cons p ps ih =>
    simp only [List.flatMap_cons, Polynomial.denoteTerms_append,
      Polynomial.denoteTerms_mulMonTerms, ih, Polynomial.denoteTerms_cons]
    grind

theorem denote_mul (ctx : Lean.Grind.CommRing.Context Rat) (p q : Polynomial Rat n) :
    (mul p q).denote ctx = p.denote ctx * q.denote ctx := by
  rw [mul, denote_normalize]
  exact denoteTerms_products ctx p.terms q.terms

theorem denote_pow (ctx : Lean.Grind.CommRing.Context Rat) (p : Polynomial Rat n) (k : Nat) :
    (pow p k).denote ctx = p.denote ctx ^ k := by
  induction k with
  | zero => simp [pow, Polynomial.denote, Polynomial.denoteTerms, Mon.denote_unit] <;> grind
  | succ k ih =>
    rw [pow, denote_mul, ih]
    grind

end Macaulean.M2.KernelPolynomial
