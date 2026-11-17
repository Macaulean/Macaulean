import Macaulean.Interpreter.KernelPolynomialSemantics

/-! Linear observations of sparse polynomials. Choosing a weight that is one
at a queried monomial and zero elsewhere gives its coefficient. The proofs do
not require sorted, distinct, or nonzero input terms. -/
namespace Macaulean.M2.KernelPolynomial
open Macaulean Lean.Grind

/-- A linear observation of a term list, independent of its sparse layout. -/
def weightedSum (weight : Mon n → Rat) : List (PolyTerm Rat n) → Rat
  | [] => 0
  | t :: ts => t.coefficient * weight t.monomial + weightedSum weight ts

theorem weightedSum_insert (weight : Mon n → Rat) (t : PolyTerm Rat n)
    (ts : List (PolyTerm Rat n)) :
    weightedSum weight (insert t ts) = t.coefficient * weight t.monomial + weightedSum weight ts := by
  induction ts with
  | nil => simp only [insert]; split <;> simp_all [weightedSum] <;> grind
  | cons u us ih =>
    simp only [insert]
    split
    · split <;> simp_all [weightedSum] <;> grind
    · next h =>
        have hm : t.monomial = u.monomial :=
          Std.LawfulEqCmp.eq_of_compare (cmp := Mon.grevlex) h
        split <;> simp_all [weightedSum] <;> grind
    · simp only [weightedSum, ih]; grind

private theorem weightedSum_fold_insert (weight : Mon n → Rat)
    (ts acc : List (PolyTerm Rat n)) :
    weightedSum weight (ts.foldl (fun xs t => insert t xs) acc) =
      weightedSum weight acc + weightedSum weight ts := by
  induction ts generalizing acc with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih =>
    simp only [List.foldl_cons, ih, weightedSum_insert, weightedSum]
    grind

theorem weightedSum_normalize (weight : Mon n → Rat) (p : Polynomial Rat n) :
    weightedSum weight (normalize p).terms = weightedSum weight p.terms := by
  simp [normalize, weightedSum_fold_insert, weightedSum]
  grind

theorem weightedSum_append (weight : Mon n → Rat) (xs ys : List (PolyTerm Rat n)) :
    weightedSum weight (xs ++ ys) = weightedSum weight xs + weightedSum weight ys := by
  induction xs with
  | nil => simp [weightedSum] <;> grind
  | cons x xs ih => simp only [List.cons_append, weightedSum, ih]; grind

theorem weightedSum_add (weight : Mon n → Rat) (p q : Polynomial Rat n) :
    weightedSum weight (add p q).terms = weightedSum weight p.terms + weightedSum weight q.terms := by
  rw [add, weightedSum_normalize]
  exact weightedSum_append weight p.terms q.terms

theorem weightedSum_neg (weight : Mon n → Rat) (p : Polynomial Rat n) :
    weightedSum weight p.neg.terms = -weightedSum weight p.terms := by
  rcases p with ⟨ts⟩
  simp only [Polynomial.neg]
  induction ts with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih => simp only [List.map_cons, weightedSum, ih]; grind

theorem weightedSum_sub (weight : Mon n → Rat) (p q : Polynomial Rat n) :
    weightedSum weight (sub p q).terms = weightedSum weight p.terms - weightedSum weight q.terms := by
  rw [sub, weightedSum_add, weightedSum_neg]
  grind

private theorem weightedSum_mulMonTerms (weight : Mon n → Rat) (c : Rat) (m : Mon n)
    (ts : List (PolyTerm Rat n)) :
    weightedSum weight (Polynomial.mulMonTerms c m ts) =
      c * weightedSum (fun k => weight (m.mul k)) ts := by
  induction ts with
  | nil => simp [Polynomial.mulMonTerms, weightedSum] <;> grind
  | cons t ts ih =>
    simp only [Polynomial.mulMonTerms, List.map_cons, weightedSum] at ih ⊢
    rw [ih]
    grind

private theorem weightedSum_products (weight : Mon n → Rat) (ps qs : List (PolyTerm Rat n)) :
    weightedSum weight (ps.flatMap fun t => Polynomial.mulMonTerms t.coefficient t.monomial qs) =
      weightedSum (fun m => weightedSum (fun k => weight (m.mul k)) qs) ps := by
  induction ps with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons, weightedSum_append, weightedSum_mulMonTerms, ih, weightedSum]

theorem weightedSum_mul (weight : Mon n → Rat) (p q : Polynomial Rat n) :
    weightedSum weight (mul p q).terms =
      weightedSum (fun m => weightedSum (fun k => weight (m.mul k)) q.terms) p.terms := by
  rw [mul, weightedSum_normalize]
  exact weightedSum_products weight p.terms q.terms

end Macaulean.M2.KernelPolynomial
