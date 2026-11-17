import Macaulean.Interpreter.KernelPolynomialWeights
import Macaulean.Verification.Views

/-! Coefficientwise laws for the production polynomial arithmetic, expressed
in the existing Stage 1 views. Convolution is the independent finite sum in
`productCoefficient`, not a definition in terms of production multiplication. -/
namespace Macaulean.M2.Verification.Views
open Macaulean.M2.KernelPolynomial Lean.Grind

private def coefficientWeight (powers : List Nat) (m : Macaulean.Mon n) : Rat :=
  if m.powers = powers then 1 else 0

private theorem coefficient_terms (ts : List (Macaulean.PolyTerm Rat n)) (powers : List Nat) :
    coefficient (ts.map fun t => (t.coefficient, t.monomial.powers)) powers =
      weightedSum (coefficientWeight powers) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, coefficient_cons, weightedSum, ih, coefficientWeight]
    split <;> grind

private theorem coeff_weighted (p : Polynomial r) (powers : List Nat) :
    p.coeff powers = weightedSum (coefficientWeight powers) p.data.terms :=
  coefficient_terms p.data.terms powers

theorem coeff_normalize (p : Polynomial r) (powers : List Nat) :
    (Polynomial.mk (normalize p.data)).coeff powers = p.coeff powers := by
  simp only [coeff_weighted, weightedSum_normalize]

theorem normalize_equivalent (p : Polynomial r) :
    Equivalent ⟨normalize p.data⟩ p := coeff_normalize p

theorem coeff_add (p q : Polynomial r) (powers : List Nat) :
    (Polynomial.mk (add p.data q.data)).coeff powers = p.coeff powers + q.coeff powers := by
  simp only [coeff_weighted, weightedSum_add]

theorem coeff_sub (p q : Polynomial r) (powers : List Nat) :
    (Polynomial.mk (sub p.data q.data)).coeff powers = p.coeff powers - q.coeff powers := by
  simp only [coeff_weighted, weightedSum_sub]

private theorem product_row (t : Macaulean.PolyTerm Rat n)
    (qs : List (Macaulean.PolyTerm Rat n)) (powers : List Nat) :
    (qs.map fun u => (u.coefficient,u.monomial.powers)).foldr
      (fun (b,bs) total =>
        (if (t.monomial.powers.zip bs).map (fun (i,j) => i+j) = powers
         then t.coefficient*b else 0) + total) 0 =
    t.coefficient * weightedSum (fun k => coefficientWeight powers (t.monomial.mul k)) qs := by
  induction qs with
  | nil => simp [weightedSum] <;> grind
  | cons u us ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih]
    have hm : (t.monomial.powers.zip u.monomial.powers).map (fun (i,j) => i+j) =
        (t.monomial.mul u.monomial).powers := by
      rw [List.map_zip_eq_zipWith]
      rfl
    simp only [weightedSum, coefficientWeight, hm]
    split <;> grind

private theorem product_terms (ps qs : List (Macaulean.PolyTerm Rat n)) (powers : List Nat) :
    (ps.map fun t => (t.coefficient,t.monomial.powers)).foldr
      (fun (a,as) total => total +
        (qs.map fun t => (t.coefficient,t.monomial.powers)).foldr
          (fun (b,bs) subtotal =>
            (if (as.zip bs).map (fun (i,j) => i+j) = powers then a*b else 0) + subtotal) 0) 0 =
    weightedSum (fun m => weightedSum (fun k => coefficientWeight powers (m.mul k)) qs) ps := by
  induction ps with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.foldr_cons, ih, product_row, weightedSum]
    grind

private theorem product_weighted (p q : Polynomial r) (powers : List Nat) :
    productCoefficient p q powers =
      weightedSum (fun m => weightedSum (fun k => coefficientWeight powers (m.mul k)) q.data.terms)
        p.data.terms := product_terms p.data.terms q.data.terms powers

theorem coeff_mul (p q : Polynomial r) (powers : List Nat) :
    (Polynomial.mk (mul p.data q.data)).coeff powers = productCoefficient p q powers := by
  simp only [coeff_weighted, weightedSum_mul, product_weighted]

theorem productCoefficient_normalize_left (p q : Polynomial r) (powers : List Nat) :
    productCoefficient ⟨normalize p.data⟩ q powers = productCoefficient p q powers := by
  simp only [product_weighted, weightedSum_normalize]

theorem productCoefficient_normalize_right (p q : Polynomial r) (powers : List Nat) :
    productCoefficient p ⟨normalize q.data⟩ powers = productCoefficient p q powers := by
  simp only [product_weighted, weightedSum_normalize]

end Macaulean.M2.Verification.Views
