import Macaulean.Interpreter.KernelPolynomialSemantics
import Macaulean.Verification.ViewLaws
import Macaulean.Verification.CoefficientLaws

/-!
# Algebraic semantics of runtime polynomial arithmetic

The public laws connect actual `evalBinOp` and `Runtime.eval` calls to the
existing `Macaulean.Polynomial.denote` and coefficientwise Stage 1 views. They hold for arbitrary same-ring typed
polynomials, including unnormalized inputs, and arbitrary variable assignments.
They do not assert correctness of `m2gbReduce`, irreducibility, or termination.
-/
namespace Macaulean.M2.Verification.PolynomialArithmetic
open Views
open Lean.Grind
abbrev Context := Lean.Grind.CommRing.Context Rat

/-- Interpretation using the project's existing polynomial semantics. -/
def denote (ctx : Context) (p : Views.Polynomial r) : Rat := p.data.denote ctx

private def result (f : Macaulean.Polynomial Rat r.names.length →
    Macaulean.Polynomial Rat r.names.length → Macaulean.Polynomial Rat r.names.length)
    (p q : Views.Polynomial r) : Views.Polynomial r :=
  ⟨KernelPolynomial.normalize (f
    (KernelPolynomial.normalize (KernelPolynomial.normalize p.data))
    (KernelPolynomial.normalize (KernelPolynomial.normalize q.data)))⟩

private theorem eval_add_result (p q : Views.Polynomial r) :
    evalBinOp .add p.value q.value = .ok (result KernelPolynomial.add p q).value := by
  simp [evalBinOp, Polynomials.evalBinary, Polynomials.common, Polynomials.polyRing?,
      Polynomials.cast, Polynomials.arithmetic, Polynomials.add_bridge,
      Polynomials.normalize_bridge, Polynomials.liftError, Except.mapError,
      Views.Polynomial.value, Views.Polynomial.raw, result, bind, Except.bind, pure, Except.pure]

private theorem eval_sub_result (p q : Views.Polynomial r) :
    evalBinOp .sub p.value q.value = .ok (result KernelPolynomial.sub p q).value := by
  simp [evalBinOp, Polynomials.evalBinary, Polynomials.common, Polynomials.polyRing?,
      Polynomials.cast, Polynomials.arithmetic, Polynomials.sub, Polynomials.binary_bridge,
      Polynomials.normalize_bridge, Polynomials.liftError, Except.mapError,
      Views.Polynomial.value, Views.Polynomial.raw, result, bind, Except.bind, pure, Except.pure]

private theorem eval_mul_result (p q : Views.Polynomial r) :
    evalBinOp .mul p.value q.value = .ok (result KernelPolynomial.mul p q).value := by
  simp [evalBinOp, Polynomials.evalBinary, Polynomials.common, Polynomials.polyRing?,
      Polynomials.cast, Polynomials.arithmetic, Polynomials.mul_bridge, Polynomials.matrixView?,
      Polynomials.normalize_bridge, Polynomials.liftError, Except.mapError,
      Views.Polynomial.value, Views.Polynomial.raw, result, bind, Except.bind, pure, Except.pure]

theorem eval_add (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .add p.value q.value = .ok out.value ∧
      ∀ ctx, denote ctx out = denote ctx p + denote ctx q := by
  refine ⟨result KernelPolynomial.add p q, ?_, ?_⟩
  · exact eval_add_result p q
  · intro ctx
    simp only [denote, result, KernelPolynomial.denote_normalize, KernelPolynomial.denote_add]

theorem eval_sub (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .sub p.value q.value = .ok out.value ∧
      ∀ ctx, denote ctx out = denote ctx p - denote ctx q := by
  refine ⟨result KernelPolynomial.sub p q, ?_, ?_⟩
  · exact eval_sub_result p q
  · intro ctx
    simp only [denote, result, KernelPolynomial.denote_normalize, KernelPolynomial.denote_sub]

theorem eval_mul (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .mul p.value q.value = .ok out.value ∧
      ∀ ctx, denote ctx out = denote ctx p * denote ctx q := by
  refine ⟨result KernelPolynomial.mul p q, ?_, ?_⟩
  · exact eval_mul_result p q
  · intro ctx
    simp only [denote, result, KernelPolynomial.denote_normalize, KernelPolynomial.denote_mul]

/-- Normalization preserves the existing coefficientwise equivalence relation. -/
theorem normalized_coefficients (p : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      Polynomials.normalized r.names.length p.raw = .ok out.raw ∧ Equivalent out p :=
  ⟨⟨KernelPolynomial.normalize p.data⟩, Polynomials.normalize_bridge p.data,
    normalize_equivalent p⟩

/-- The actual operator satisfies the existing coefficient specification. -/
theorem eval_add_coefficients (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .add p.value q.value = .ok out.value ∧
      ∀ powers, out.coeff powers = p.coeff powers + q.coeff powers := by
  refine ⟨result KernelPolynomial.add p q, eval_add_result p q, ?_⟩
  intro powers
  let pn : Views.Polynomial r := ⟨KernelPolynomial.normalize (KernelPolynomial.normalize p.data)⟩
  let qn : Views.Polynomial r := ⟨KernelPolynomial.normalize (KernelPolynomial.normalize q.data)⟩
  change (Views.Polynomial.mk (KernelPolynomial.normalize (KernelPolynomial.add pn.data qn.data))).coeff powers = _
  rw [coeff_normalize ⟨KernelPolynomial.add pn.data qn.data⟩, coeff_add pn qn]
  rw [coeff_normalize ⟨KernelPolynomial.normalize p.data⟩, coeff_normalize p,
    coeff_normalize ⟨KernelPolynomial.normalize q.data⟩, coeff_normalize q]

/-- The actual operator satisfies the existing coefficient specification. -/
theorem eval_sub_coefficients (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .sub p.value q.value = .ok out.value ∧
      ∀ powers, out.coeff powers = p.coeff powers - q.coeff powers := by
  refine ⟨result KernelPolynomial.sub p q, eval_sub_result p q, ?_⟩
  intro powers
  let pn : Views.Polynomial r := ⟨KernelPolynomial.normalize (KernelPolynomial.normalize p.data)⟩
  let qn : Views.Polynomial r := ⟨KernelPolynomial.normalize (KernelPolynomial.normalize q.data)⟩
  change (Views.Polynomial.mk (KernelPolynomial.normalize (KernelPolynomial.sub pn.data qn.data))).coeff powers = _
  rw [coeff_normalize ⟨KernelPolynomial.sub pn.data qn.data⟩, coeff_sub pn qn]
  rw [coeff_normalize ⟨KernelPolynomial.normalize p.data⟩, coeff_normalize p,
    coeff_normalize ⟨KernelPolynomial.normalize q.data⟩, coeff_normalize q]

/-- The actual operator satisfies the existing coefficient specification. -/
theorem eval_mul_coefficients (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .mul p.value q.value = .ok out.value ∧
      ∀ powers, out.coeff powers = productCoefficient p q powers := by
  refine ⟨result KernelPolynomial.mul p q, eval_mul_result p q, ?_⟩
  intro powers
  let pn : Views.Polynomial r := ⟨KernelPolynomial.normalize (KernelPolynomial.normalize p.data)⟩
  let qn : Views.Polynomial r := ⟨KernelPolynomial.normalize (KernelPolynomial.normalize q.data)⟩
  change (Views.Polynomial.mk (KernelPolynomial.normalize (KernelPolynomial.mul pn.data qn.data))).coeff powers = _
  rw [coeff_normalize ⟨KernelPolynomial.mul pn.data qn.data⟩, coeff_mul pn qn]
  rw [productCoefficient_normalize_left ⟨KernelPolynomial.normalize p.data⟩,
    productCoefficient_normalize_left p,
    productCoefficient_normalize_right p ⟨KernelPolynomial.normalize q.data⟩,
    productCoefficient_normalize_right p q]

/-- Arithmetic does not allocate or mutate after its operands have evaluated.
Operand effects are retained in `s₂`; no purity assumption on those operands is
made. The equation describes the real lexical evaluator at any fuel budget. -/
theorem runtime_binary (op : BinOp) (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State)
    (p q out : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂))
    (hop : evalBinOp op p.value q.value = .ok out.value) :
    Runtime.eval (fuel + 1) (.binop op a b) frames s = .ok (out.value, s₂) := by
  cases op <;>
    simp_all [Runtime.eval, Views.Polynomial.value, Runtime.liftResult,
      Except.mapError, bind, Except.bind, pure, Except.pure]

theorem runtime_add (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State) (p q : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂)) :
    ∃ out : Views.Polynomial r,
      Runtime.eval (fuel + 1) (.binop .add a b) frames s = .ok (out.value, s₂) ∧
      ∀ ctx, denote ctx out = denote ctx p + denote ctx q := by
  obtain ⟨out, he, hd⟩ := eval_add p q
  exact ⟨out, runtime_binary .add fuel a b frames s s₁ s₂ p q out ha hb he, hd⟩

theorem runtime_sub (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State) (p q : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂)) :
    ∃ out : Views.Polynomial r,
      Runtime.eval (fuel + 1) (.binop .sub a b) frames s = .ok (out.value, s₂) ∧
      ∀ ctx, denote ctx out = denote ctx p - denote ctx q := by
  obtain ⟨out, he, hd⟩ := eval_sub p q
  exact ⟨out, runtime_binary .sub fuel a b frames s s₁ s₂ p q out ha hb he, hd⟩

theorem runtime_mul (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State) (p q : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂)) :
    ∃ out : Views.Polynomial r,
      Runtime.eval (fuel + 1) (.binop .mul a b) frames s = .ok (out.value, s₂) ∧
      ∀ ctx, denote ctx out = denote ctx p * denote ctx q := by
  obtain ⟨out, he, hd⟩ := eval_mul p q
  exact ⟨out, runtime_binary .mul fuel a b frames s s₁ s₂ p q out ha hb he, hd⟩

theorem successful_add (p q out : Views.Polynomial r)
    (h : evalBinOp .add p.value q.value = .ok out.value) (ctx : Context) :
    denote ctx out = denote ctx p + denote ctx q := by
  obtain ⟨actual, he, hd⟩ := eval_add p q
  have same := polynomial_value_injective actual out (Except.ok.inj (he.symm.trans h))
  subst actual
  exact hd ctx

theorem successful_sub (p q out : Views.Polynomial r)
    (h : evalBinOp .sub p.value q.value = .ok out.value) (ctx : Context) :
    denote ctx out = denote ctx p - denote ctx q := by
  obtain ⟨actual, he, hd⟩ := eval_sub p q
  have same := polynomial_value_injective actual out (Except.ok.inj (he.symm.trans h))
  subst actual
  exact hd ctx

theorem successful_mul (p q out : Views.Polynomial r)
    (h : evalBinOp .mul p.value q.value = .ok out.value) (ctx : Context) :
    denote ctx out = denote ctx p * denote ctx q := by
  obtain ⟨actual, he, hd⟩ := eval_mul p q
  have same := polynomial_value_injective actual out (Except.ok.inj (he.symm.trans h))
  subst actual
  exact hd ctx

theorem successful_add_coefficients (p q out : Views.Polynomial r)
    (h : evalBinOp .add p.value q.value = .ok out.value) (powers : List Nat) :
    out.coeff powers = p.coeff powers + q.coeff powers := by
  obtain ⟨actual, he, hc⟩ := eval_add_coefficients p q
  have same := polynomial_value_injective actual out (Except.ok.inj (he.symm.trans h))
  subst actual
  exact hc powers

theorem runtime_add_coefficients (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State) (p q : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂)) :
    ∃ out : Views.Polynomial r,
      Runtime.eval (fuel + 1) (.binop .add a b) frames s = .ok (out.value, s₂) ∧
      ∀ powers, out.coeff powers = p.coeff powers + q.coeff powers := by
  obtain ⟨out, he, hc⟩ := eval_add_coefficients p q
  exact ⟨out, runtime_binary .add fuel a b frames s s₁ s₂ p q out ha hb he, hc⟩

theorem successful_sub_coefficients (p q out : Views.Polynomial r)
    (h : evalBinOp .sub p.value q.value = .ok out.value) (powers : List Nat) :
    out.coeff powers = p.coeff powers - q.coeff powers := by
  obtain ⟨actual, he, hc⟩ := eval_sub_coefficients p q
  have same := polynomial_value_injective actual out (Except.ok.inj (he.symm.trans h))
  subst actual
  exact hc powers

theorem runtime_sub_coefficients (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State) (p q : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂)) :
    ∃ out : Views.Polynomial r,
      Runtime.eval (fuel + 1) (.binop .sub a b) frames s = .ok (out.value, s₂) ∧
      ∀ powers, out.coeff powers = p.coeff powers - q.coeff powers := by
  obtain ⟨out, he, hc⟩ := eval_sub_coefficients p q
  exact ⟨out, runtime_binary .sub fuel a b frames s s₁ s₂ p q out ha hb he, hc⟩

theorem successful_mul_coefficients (p q out : Views.Polynomial r)
    (h : evalBinOp .mul p.value q.value = .ok out.value) (powers : List Nat) :
    out.coeff powers = productCoefficient p q powers := by
  obtain ⟨actual, he, hc⟩ := eval_mul_coefficients p q
  have same := polynomial_value_injective actual out (Except.ok.inj (he.symm.trans h))
  subst actual
  exact hc powers

theorem runtime_mul_coefficients (fuel : Nat) (a b : Lexical.Code)
    (frames : Runtime.Frames) (s s₁ s₂ : Runtime.State) (p q : Views.Polynomial r)
    (ha : Runtime.eval fuel a frames s = .ok (p.value, s₁))
    (hb : Runtime.eval fuel b frames s₁ = .ok (q.value, s₂)) :
    ∃ out : Views.Polynomial r,
      Runtime.eval (fuel + 1) (.binop .mul a b) frames s = .ok (out.value, s₂) ∧
      ∀ powers, out.coeff powers = productCoefficient p q powers := by
  obtain ⟨out, he, hc⟩ := eval_mul_coefficients p q
  exact ⟨out, runtime_binary .mul fuel a b frames s s₁ s₂ p q out ha hb he, hc⟩

/-- The no-divisor update in `m2gbReduce` preserves pending plus remainder.
This proves its arithmetic for any chosen term; selection of the leading term
and control flow through the function remain separate obligations. -/
theorem move_balance (pending remainder term nextPending nextRemainder : Views.Polynomial r)
    (hp : evalBinOp .sub pending.value term.value = .ok nextPending.value)
    (hr : evalBinOp .add remainder.value term.value = .ok nextRemainder.value)
    (ctx : Context) :
    denote ctx nextPending + denote ctx nextRemainder =
      denote ctx pending + denote ctx remainder := by
  rw [successful_sub pending term nextPending hp, successful_add remainder term nextRemainder hr]
  grind

/-- The divisor update removes precisely the chosen multiple. A later proof
must connect coefficient-row updates and the recursive call to this equation. -/
theorem cancel_balance (pending remainder coefficient reducer product nextPending : Views.Polynomial r)
    (hm : evalBinOp .mul coefficient.value reducer.value = .ok product.value)
    (hs : evalBinOp .sub pending.value product.value = .ok nextPending.value)
    (ctx : Context) :
    denote ctx nextPending + denote ctx remainder =
      (denote ctx pending + denote ctx remainder) - denote ctx coefficient * denote ctx reducer := by
  rw [successful_sub pending product nextPending hs, successful_mul coefficient reducer product hm]
  grind

/-- The successful result is coefficientwise equivalent to the polynomial operation. -/
theorem successful_add_equivalent (p q out : Views.Polynomial r)
    (h : evalBinOp .add p.value q.value = .ok out.value) :
    Equivalent out ⟨KernelPolynomial.add p.data q.data⟩ := fun powers =>
  (successful_add_coefficients p q out h powers).trans (coeff_add p q powers).symm

/-- The successful result is coefficientwise equivalent to the polynomial operation. -/
theorem successful_sub_equivalent (p q out : Views.Polynomial r)
    (h : evalBinOp .sub p.value q.value = .ok out.value) :
    Equivalent out ⟨KernelPolynomial.sub p.data q.data⟩ := fun powers =>
  (successful_sub_coefficients p q out h powers).trans (coeff_sub p q powers).symm

/-- The successful result is coefficientwise equivalent to the polynomial operation. -/
theorem successful_mul_equivalent (p q out : Views.Polynomial r)
    (h : evalBinOp .mul p.value q.value = .ok out.value) :
    Equivalent out ⟨KernelPolynomial.mul p.data q.data⟩ := fun powers =>
  (successful_mul_coefficients p q out h powers).trans (coeff_mul p q powers).symm

/-- Coefficientwise balance for moving a term into the remainder. -/
theorem move_balance_coefficients (pending remainder term nextPending nextRemainder : Views.Polynomial r)
    (hp : evalBinOp .sub pending.value term.value = .ok nextPending.value)
    (hr : evalBinOp .add remainder.value term.value = .ok nextRemainder.value)
    (powers : List Nat) :
    nextPending.coeff powers + nextRemainder.coeff powers =
      pending.coeff powers + remainder.coeff powers := by
  rw [successful_sub_coefficients pending term nextPending hp,
    successful_add_coefficients remainder term nextRemainder hr]
  grind

/-- Coefficientwise balance for subtracting the selected multiple of a reducer. -/
theorem cancel_balance_coefficients (pending remainder coefficient reducer product nextPending : Views.Polynomial r)
    (hm : evalBinOp .mul coefficient.value reducer.value = .ok product.value)
    (hs : evalBinOp .sub pending.value product.value = .ok nextPending.value)
    (powers : List Nat) :
    nextPending.coeff powers + remainder.coeff powers =
      (pending.coeff powers + remainder.coeff powers) - productCoefficient coefficient reducer powers := by
  rw [successful_sub_coefficients pending product nextPending hs,
    successful_mul_coefficients coefficient reducer product hm]
  grind

end Macaulean.M2.Verification.PolynomialArithmetic
