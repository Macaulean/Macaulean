import Macaulean.Interpreter.GCD.Algebra
import Macaulean.Interpreter.GCD.Arithmetic

/-! Monic normalization and divisibility for the production scalar operation. -/
namespace Macaulean.M2.GCD.Univariate
open Macaulean KernelPolynomial Lean.Grind

def scale (c : Rat) (p : Poly) : Poly := normalize (Polynomial.smul c p)

private theorem weight_removeZeros (w : Mon 1 → Rat) (ts : List Term) :
    weightedSum w (Polynomial.removeZeros ts) = weightedSum w ts := by
  simp only [Polynomial.removeZeros]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    by_cases hc : t.coefficient = 0
    · simp [hc, weightedSum, ih] <;> grind
    · simp [hc, weightedSum, ih]

theorem coeff_scale (c : Rat) (p : Poly) (k : Nat) :
    coeff (scale c p).terms k = c * coeff p.terms k := by
  unfold scale coeff
  rw [weightedSum_normalize]
  simp only [Polynomial.smul]
  rw [weight_removeZeros]
  induction p.terms with
  | nil => simp [weightedSum] <;> grind
  | cons t ts ih =>
    simp only [List.map_cons, weightedSum, ih]
    grind

theorem scale_eq_mul (c : Rat) (p : Poly) :
    scale c p = KernelPolynomial.mul (monomial c 0) p := by
  apply polynomial_ext (normalize_canonical _) (mul_canonical ..)
  intro k
  change coeff (scale c p).terms k = _
  rw [coeff_scale]
  simpa using (coeff_mul_monomial c 0 k p).symm

private theorem scaled_canonical (c : Rat) (hc : c ≠ 0) (ts : List Term)
    (h : Canonical ts) :
    Canonical (ts.map fun t => ⟨c*t.coefficient,t.monomial⟩) := by
  induction h with
  | nil => exact .nil
  | @cons t ts ht hb hts ih =>
    apply Canonical.cons
    · intro hz
      rcases Rat.mul_eq_zero.mp hz with h | h
      · exact hc h
      · exact ht h
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      exact hb v hv
    · exact ih

private theorem removeZeros_canonical (ts : List Term) (h : Canonical ts) :
    Polynomial.removeZeros ts = ts := by
  apply List.filter_eq_self.mpr
  intro t ht
  simp [canonical_nonzero h ht]

theorem scale_terms (c : Rat) (hc : c ≠ 0) (p : Poly) (hp : Canonical p.terms) :
    (scale c p).terms = p.terms.map (fun t => ⟨c*t.coefficient,t.monomial⟩) := by
  have hs := scaled_canonical c hc p.terms hp
  unfold scale
  simp only [Polynomial.smul, removeZeros_canonical _ hs]
  rw [normalize_eq_self _ hs]

theorem reciprocal_ne_zero (c : Rat) (hc : c ≠ 0) : (1 : Rat)/c ≠ 0 := by
  intro hz
  have h := Rat.div_mul_cancel (a := 1) hc
  rw [hz, Rat.zero_mul] at h
  exact (by decide : (0 : Rat) ≠ 1) h

theorem mul_monomials (a b : Rat) (i j : Nat) :
    KernelPolynomial.mul (monomial a i) (monomial b j) =
      normalize (monomial (a*b) (i+j)) := rfl

theorem scalar_inverse (c : Rat) (hc : c ≠ 0) :
    KernelPolynomial.mul (monomial (1/c) 0) (monomial c 0) = monomial 1 0 := by
  rw [mul_monomials, Rat.div_mul_cancel hc]
  exact normalize_eq_self _ (monomial_canonical 1 0 (by decide))

theorem divides_trans (a b c : Poly) (hab : Divides a b) (hbc : Divides b c) :
    Divides a c := by
  obtain ⟨u, rfl⟩ := hab
  obtain ⟨v, rfl⟩ := hbc
  exact ⟨KernelPolynomial.mul u v, mul_assoc a u v⟩

theorem divides_scale_iff (c : Rat) (hc : c ≠ 0) (d f : Poly)
    (hf : Canonical f.terms) : Divides d (scale c f) ↔ Divides d f := by
  rw [scale_eq_mul]
  constructor
  · intro h
    have hi := divides_mul d _ (monomial (1/c) 0) h
    rw [← mul_assoc, scalar_inverse c hc, one_mul, normalize_eq_self f hf] at hi
    exact hi
  · exact divides_mul d f _

theorem scale_divides_iff (c : Rat) (hc : c ≠ 0) (f g : Poly)
    (hf : Canonical f.terms) : Divides (scale c f) g ↔ Divides f g := by
  have hs : Canonical (scale c f).terms := normalize_canonical _
  have forward : Divides f (scale c f) :=
    (divides_scale_iff c hc f f hf).mpr (divides_self f hf)
  have backward : Divides (scale c f) f :=
    (divides_scale_iff c hc (scale c f) f hf).mp (divides_self _ hs)
  exact ⟨divides_trans f _ g forward, divides_trans _ f g backward⟩

def monicNormalize (p : Poly) : Poly :=
  match p.terms with
  | [] => p
  | t :: _ => scale (1/t.coefficient) p

def MonicOrZero (p : Poly) : Prop :=
  match p.terms with
  | [] => True
  | t :: _ => t.coefficient = 1

theorem monicNormalize_canonical (p : Poly) (hp : Canonical p.terms) :
    Canonical (monicNormalize p).terms := by
  cases p with
  | mk ts =>
    cases ts with
    | nil => exact hp
    | cons t ts => exact normalize_canonical _

theorem monicNormalize_monic (p : Poly) (hp : Canonical p.terms) :
    MonicOrZero (monicNormalize p) := by
  cases p with
  | mk ts =>
    cases ts with
    | nil => trivial
    | cons t ts =>
      have ht := canonical_nonzero hp List.mem_cons_self
      simp only [monicNormalize, MonicOrZero,
        scale_terms _ (reciprocal_ne_zero _ ht) _ hp, List.map_cons]
      exact Rat.div_mul_cancel ht

theorem monicNormalize_divides (f g : Poly) (hf : Canonical f.terms) :
    Divides (monicNormalize f) g ↔ Divides f g := by
  cases f with
  | mk ts =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      exact scale_divides_iff _ (reciprocal_ne_zero _
        (canonical_nonzero hf List.mem_cons_self)) _ _ hf

theorem divides_monicNormalize (d f : Poly) (hf : Canonical f.terms) :
    Divides d (monicNormalize f) ↔ Divides d f := by
  cases f with
  | mk ts =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      exact divides_scale_iff _ (reciprocal_ne_zero _
        (canonical_nonzero hf List.mem_cons_self)) _ _ hf

theorem eval_div_scalar (id : Nat) (name : String) (p : Poly) (c : Rat)
    (hp : Canonical p.terms) (hc : c ≠ 0) :
    evalBinOp .div (value id name p) (.qq c) =
      .ok (value id name (scale (1/c) p)) := by
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.asPolynomial,
    Polynomials.normalize_bridge, normalize_eq_self p hp, Polynomials.scalar?, hc,
    Polynomials.smul, Polynomials.unary_bridge, scale,
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem eval_eq_zero (id : Nat) (name : String) (p : Poly)
    (hp : Canonical p.terms) :
    evalBinOp .eq (value id name p) (.zz 0) = .ok (.bool p.terms.isEmpty) := by
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.equal,
    Polynomials.matrixView?, Polynomials.common, Polynomials.polyRing?, Polynomials.cast,
    Polynomials.normalize_bridge, normalize_eq_self p hp, Polynomials.scalar?,
    Polynomials.constant, Polynomials.liftError, Except.mapError, bind, Except.bind,
    pure, Except.pure]
  cases p with
  | mk ts => cases ts <;> rfl

theorem eval_add (id : Nat) (name : String) (p q : Poly)
    (hp : Canonical p.terms) (hq : Canonical q.terms) :
    evalBinOp .add (value id name p) (value id name q) =
      .ok (value id name (KernelPolynomial.add p q)) := by
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.common,
    Polynomials.polyRing?, Polynomials.cast, Polynomials.arithmetic,
    Polynomials.add, Polynomials.binary_bridge, Polynomials.normalize_bridge,
    normalize_eq_self p hp, normalize_eq_self q hq,
    normalize_eq_self _ (add_canonical p q),
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem eval_mul_scalar (id : Nat) (name : String) (c : Rat) (p : Poly)
    (hc : c ≠ 0) (hp : Canonical p.terms) :
    evalBinOp .mul (.qq c) (value id name p) =
      .ok (value id name (scale c p)) := by
  have hconstant : Polynomials.constant 1 c = Polynomials.encode (monomial c 0) := by
    simp [Polynomials.constant, hc, Polynomials.encode, monomial]
  rw [scale_eq_mul]
  simp [value, ringInfo, evalBinOp, Polynomials.evalBinary, Polynomials.common,
    Polynomials.polyRing?, Polynomials.cast, Polynomials.scalar?, Polynomials.arithmetic,
    Polynomials.matrixView?, hconstant, Polynomials.mul_bridge, Polynomials.normalize_bridge,
    normalize_eq_self p hp, normalize_eq_self _ (monomial_canonical c 0 hc),
    normalize_eq_self _ (mul_canonical ..),
    Polynomials.liftError, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem eval_mul_scalar_monomial (id : Nat) (name : String) (c : Rat) (k : Nat)
    (hc : c ≠ 0) :
    evalBinOp .mul (.qq c) (value id name (monomial 1 k)) =
      .ok (value id name (monomial c k)) := by
  rw [eval_mul_scalar id name c _ hc (monomial_canonical 1 k (by decide)),
    scale_eq_mul, mul_monomials]
  simp only [Rat.mul_one, Nat.zero_add, normalize_eq_self _ (monomial_canonical c k hc)]

end Macaulean.M2.GCD.Univariate
