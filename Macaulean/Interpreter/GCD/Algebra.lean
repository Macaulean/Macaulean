import Macaulean.Interpreter.GCD.Univariate

/-!
Algebraic identities for the actual kernel polynomial operations. Equality is
equality of canonical sparse polynomials, justified coefficientwise; evaluating
at a few rational points is not used as a substitute for polynomial equality.
-/
namespace Macaulean.M2.GCD.Univariate
open Macaulean KernelPolynomial Lean.Grind

private theorem weight_add (f g : Mon 1 → Rat) (ts : List Term) :
    weightedSum (fun m => f m + g m) ts = weightedSum f ts + weightedSum g ts := by
  induction ts with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih => simp only [weightedSum, ih]; grind

private theorem weight_sub (f g : Mon 1 → Rat) (ts : List Term) :
    weightedSum (fun m => f m - g m) ts = weightedSum f ts - weightedSum g ts := by
  induction ts with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih => simp only [weightedSum, ih]; grind

private theorem weight_scale (c : Rat) (f : Mon 1 → Rat) (ts : List Term) :
    weightedSum (fun m => c * f m) ts = c * weightedSum f ts := by
  induction ts with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih => simp only [weightedSum, ih]; grind

private theorem weight_zero (ts : List Term) : weightedSum (fun _ => 0) ts = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [weightedSum, ih]; grind

private theorem weight_swap (w : Mon 1 → Mon 1 → Rat) (ps qs : List Term) :
    weightedSum (fun m => weightedSum (w m) qs) ps =
      weightedSum (fun n => weightedSum (fun m => w m n) ps) qs := by
  induction ps with
  | nil => simp only [weightedSum, weight_zero]
  | cons t ts ih =>
    simp only [weightedSum, weight_add, weight_scale, ih]

private theorem mon_mul_assoc (a b c : Mon 1) : (a.mul b).mul c = a.mul (b.mul c) := by
  apply mon_eq_of_degree_eq
  simp only [degree_mul]
  omega

private theorem mon_mul_comm (a b : Mon 1) : a.mul b = b.mul a := by
  apply mon_eq_of_degree_eq
  simp only [degree_mul]
  omega

private theorem multiplication_canonical (p q : Poly) :
    Canonical (KernelPolynomial.mul p q).terms := normalize_canonical _

theorem add_canonical (p q : Poly) : Canonical (KernelPolynomial.add p q).terms :=
  normalize_canonical _

theorem coeff_add (p q : Poly) (k : Nat) :
    coeff (KernelPolynomial.add p q).terms k = coeff p.terms k + coeff q.terms k :=
  weightedSum_add _ p q

theorem mul_assoc (p q r : Poly) :
    KernelPolynomial.mul (KernelPolynomial.mul p q) r =
      KernelPolynomial.mul p (KernelPolynomial.mul q r) := by
  apply polynomial_ext (multiplication_canonical ..) (multiplication_canonical ..)
  intro k
  simp only [coeff, weightedSum_mul, mon_mul_assoc]

theorem mul_comm (p q : Poly) :
    KernelPolynomial.mul p q = KernelPolynomial.mul q p := by
  apply polynomial_ext (multiplication_canonical ..) (multiplication_canonical ..)
  intro k
  simp only [coeff, weightedSum_mul]
  rw [weight_swap]
  simp only [mon_mul_comm]

theorem mul_add (p q r : Poly) :
    KernelPolynomial.mul p (KernelPolynomial.add q r) =
      KernelPolynomial.add (KernelPolynomial.mul p q) (KernelPolynomial.mul p r) := by
  apply polynomial_ext (multiplication_canonical ..) (add_canonical ..)
  intro k
  simp only [coeff, weightedSum_mul, weightedSum_add, weight_add]

theorem mul_sub (p q r : Poly) :
    KernelPolynomial.mul p (KernelPolynomial.sub q r) =
      KernelPolynomial.sub (KernelPolynomial.mul p q) (KernelPolynomial.mul p r) := by
  apply polynomial_ext (multiplication_canonical ..) (sub_canonical ..)
  intro k
  simp only [coeff, weightedSum_mul, weightedSum_sub, weight_sub]

theorem mul_one (p : Poly) :
    KernelPolynomial.mul p (monomial 1 0) = normalize p := by
  apply polynomial_ext (multiplication_canonical ..) (normalize_canonical _)
  intro k
  simp only [coeff, weightedSum_mul, weightedSum_normalize, monomial,
    weightedSum, degree_mul]
  simp [Mon.degree, Rat.one_mul, Rat.add_zero]
  rfl

theorem one_mul (p : Poly) :
    KernelPolynomial.mul (monomial 1 0) p = normalize p := by
  rw [mul_comm, mul_one]

theorem mul_zero (p : Poly) : KernelPolynomial.mul p ⟨[]⟩ = ⟨[]⟩ := by
  apply polynomial_ext (multiplication_canonical ..) Canonical.nil
  intro k
  simp only [coeff, weightedSum_mul, weightedSum, weight_zero]

theorem sub_add_cancel (p q : Poly) (hp : Canonical p.terms) :
    KernelPolynomial.add (KernelPolynomial.sub p q) q = p := by
  apply polynomial_ext (add_canonical ..) hp
  intro k
  rw [coeff_add, coeff_sub]
  grind

/-- Polynomial divisibility with an actual polynomial quotient witness. -/
def Divides (d f : Poly) : Prop := ∃ q : Poly, f = KernelPolynomial.mul d q

theorem divides_self (p : Poly) (hp : Canonical p.terms) : Divides p p := by
  refine ⟨monomial 1 0, ?_⟩
  rw [mul_one, normalize_eq_self p hp]

theorem divides_zero (p : Poly) : Divides p ⟨[]⟩ := ⟨⟨[]⟩, (mul_zero p).symm⟩

theorem divides_mul (d p q : Poly) (hp : Divides d p) :
    Divides d (KernelPolynomial.mul q p) := by
  obtain ⟨a, rfl⟩ := hp
  refine ⟨KernelPolynomial.mul q a, ?_⟩
  rw [← mul_assoc q d a, mul_comm q d, mul_assoc]

theorem divides_add (d p q : Poly) (hp : Divides d p) (hq : Divides d q) :
    Divides d (KernelPolynomial.add p q) := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  exact ⟨KernelPolynomial.add a b, (mul_add d a b).symm⟩

theorem divides_sub (d p q : Poly) (hp : Divides d p) (hq : Divides d q) :
    Divides d (KernelPolynomial.sub p q) := by
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  exact ⟨KernelPolynomial.sub a b, (mul_sub d a b).symm⟩

/-- Leading-term cancellation preserves exactly the common polynomial divisors.
The quotient can be any polynomial, so this covers every reduction step. -/
theorem common_divisors_sub (f g q d : Poly) (hf : Canonical f.terms) :
    (Divides d g ∧ Divides d (KernelPolynomial.sub f (KernelPolynomial.mul q g))) ↔
      (Divides d f ∧ Divides d g) := by
  constructor
  · rintro ⟨hg, hr⟩
    have hsum := divides_add d _ _ hr (divides_mul d g q hg)
    rw [sub_add_cancel f _ hf] at hsum
    exact ⟨hsum, hg⟩
  · rintro ⟨hf, hg⟩
    exact ⟨hg, divides_sub d f _ hf (divides_mul d g q hg)⟩

end Macaulean.M2.GCD.Univariate
