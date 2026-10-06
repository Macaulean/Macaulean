import Macaulean.Interpreter.KernelPolynomialSemantics
import Macaulean.Verification.ViewLaws

/-!
# Algebraic semantics of runtime polynomial arithmetic

The public laws connect actual `evalBinOp` and `Runtime.eval` calls to the
existing `Macaulean.Polynomial.denote`. They hold for arbitrary same-ring typed
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

theorem eval_add (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .add p.value q.value = .ok out.value ∧
      ∀ ctx, denote ctx out = denote ctx p + denote ctx q := by
  refine ⟨result KernelPolynomial.add p q, ?_, ?_⟩
  · simp [evalBinOp, Polynomials.evalBinary, Polynomials.common, Polynomials.polyRing?,
      Polynomials.cast, Polynomials.arithmetic, Polynomials.add_bridge,
      Polynomials.normalize_bridge, Polynomials.liftError, Except.mapError,
      Views.Polynomial.value, Views.Polynomial.raw, result, bind, Except.bind, pure, Except.pure]
  · intro ctx
    simp only [denote, result, KernelPolynomial.denote_normalize, KernelPolynomial.denote_add]

theorem eval_sub (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .sub p.value q.value = .ok out.value ∧
      ∀ ctx, denote ctx out = denote ctx p - denote ctx q := by
  refine ⟨result KernelPolynomial.sub p q, ?_, ?_⟩
  · simp [evalBinOp, Polynomials.evalBinary, Polynomials.common, Polynomials.polyRing?,
      Polynomials.cast, Polynomials.arithmetic, Polynomials.sub, Polynomials.binary_bridge,
      Polynomials.normalize_bridge, Polynomials.liftError, Except.mapError,
      Views.Polynomial.value, Views.Polynomial.raw, result, bind, Except.bind, pure, Except.pure]
  · intro ctx
    simp only [denote, result, KernelPolynomial.denote_normalize, KernelPolynomial.denote_sub]

theorem eval_mul (p q : Views.Polynomial r) :
    ∃ out : Views.Polynomial r,
      evalBinOp .mul p.value q.value = .ok out.value ∧
      ∀ ctx, denote ctx out = denote ctx p * denote ctx q := by
  refine ⟨result KernelPolynomial.mul p q, ?_, ?_⟩
  · simp [evalBinOp, Polynomials.evalBinary, Polynomials.common, Polynomials.polyRing?,
      Polynomials.cast, Polynomials.arithmetic, Polynomials.mul_bridge, Polynomials.matrixView?,
      Polynomials.normalize_bridge, Polynomials.liftError, Except.mapError,
      Views.Polynomial.value, Views.Polynomial.raw, result, bind, Except.bind, pure, Except.pure]
  · intro ctx
    simp only [denote, result, KernelPolynomial.denote_normalize, KernelPolynomial.denote_mul]

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

end Macaulean.M2.Verification.PolynomialArithmetic
