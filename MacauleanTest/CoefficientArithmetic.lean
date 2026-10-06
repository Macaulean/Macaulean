import Macaulean.Verification.PolynomialArithmetic
import Macaulean.Interpreter.Run

/-! Coefficient contracts exercised on noncanonical data, actual source, and
stateful runtime operands. All finite execution witnesses are kernel checked. -/
namespace Macaulean.M2.Verification.PolynomialArithmetic.CoefficientTests
open Views
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private def ring : Polynomials.RingInfo := ⟨0,["x","y"]⟩
private def poly (terms : List (Rat × Nat × Nat)) : Views.Polynomial ring :=
  ⟨⟨terms.map fun (c,i,j) => ⟨c,⟨[i,j],rfl⟩⟩⟩⟩

-- p represents 2y. Both operands include unsorted terms, duplicate monomials,
-- zeros, cancellation, and rational coefficients; the product is 6xy - 2y.
private def p := poly [(1/2,1,0),(2,0,1),(-1,1,0),(0,4,2),(1/2,1,0)]
private def q := poly [(-1,0,0),(3/2,1,0),(3/2,1,0),(0,0,4)]
private def product := poly [(6,1,1),(-2,0,1)]

private theorem product_execution :
    evalBinOp .mul p.value q.value = .ok product.value := by decide +kernel

theorem product_all_coefficients (powers : List Nat) :
    product.coeff powers = productCoefficient p q powers :=
  successful_mul_coefficients p q product product_execution powers

theorem product_equivalent : Equivalent product ⟨KernelPolynomial.mul p.data q.data⟩ :=
  successful_mul_equivalent p q product product_execution

example (powers : List Nat) : (poly [(3,1,0),(2,0,1),(-1,0,0)]).coeff powers =
    p.coeff powers + q.coeff powers :=
  successful_add_coefficients p q _ (by decide +kernel) powers
example (powers : List Nat) : (poly [(-3,1,0),(2,0,1),(1,0,0)]).coeff powers =
    p.coeff powers - q.coeff powers :=
  successful_sub_coefficients p q _ (by decide +kernel) powers

example : Polynomials.normalized ring.names.length p.raw = .ok (poly [(2,0,1)]).raw :=
  by decide +kernel
example : Equivalent ⟨KernelPolynomial.normalize p.data⟩ p := normalize_equivalent p
example : product.coeff [] = 0 ∧ product.coeff [1] = 0 ∧ product.coeff [1,1,0] = 0 :=
  by decide +kernel

-- Reject an incorrect coefficient using the same coefficientwise equivalence.
example : ¬Equivalent product (poly [(5,1,1),(-2,0,1)]) := by
  intro h
  have wrong : product.coeff [1,1] ≠ (poly [(5,1,1),(-2,0,1)]).coeff [1,1] := by decide +kernel
  exact wrong (h [1,1])

private def constantRing : Polynomials.RingInfo := ⟨1,[]⟩
private def constant (c : Rat) : Views.Polynomial constantRing := ⟨⟨[⟨c,⟨[],rfl⟩⟩]⟩⟩
example (powers : List Nat) : (constant 6).coeff powers =
    productCoefficient (constant 2) (constant 3) powers :=
  successful_mul_coefficients _ _ _ (by decide +kernel) powers
example (powers : List Nat) : (poly []).coeff powers = p.coeff powers - p.coeff powers :=
  successful_sub_coefficients p p _ (by decide +kernel) powers

-- An existing Stage 1 representation relation can consume the theorem directly.
-- No new contract definition or assumed arithmetic law is needed.
theorem product_represents (a b out : Views.Polynomial r)
    (h : evalBinOp .mul a.value b.value = .ok out.value) :
    Represents out [b] ⟨[a],rfl⟩ := by
  intro powers
  simp only [linearCoefficient]
  rw [successful_mul_coefficients a b out h]
  grind

theorem source_coefficients :
    run "R=QQ[x,y];(x+y)*(x-y)" = .ok (poly [(1,2,0),(-1,0,2)]).value ∧
    ∀ powers, (poly [(1,2,0),(-1,0,2)]).coeff powers =
      productCoefficient (poly [(1,1,0),(1,0,1)]) (poly [(1,1,0),(-1,0,1)]) powers := by
  constructor
  · decide +kernel
  · exact successful_mul_coefficients _ _ _ (by decide +kernel)

-- The right operand sees the left operand's write. The coefficient theorem is
-- generic in the polynomial, ring, and exponent query, not a finite grid test.
theorem effectful_coefficients (a : Views.Polynomial r) :
    let initial : Runtime.State := { env := [], heap := { cells := [.null, a.value] } }
    let after : Runtime.State := { env := [], heap := { cells := [a.value, a.value] } }
    ∃ out : Views.Polynomial r,
      Runtime.eval 3
        (.binop .mul (.set (.slot 0 0) (.read (.slot 0 1))) (.read (.slot 0 0)))
        [[0,1]] initial = .ok (out.value, after) ∧
      ∀ powers, out.coeff powers = productCoefficient a a powers := by
  dsimp only
  apply runtime_mul_coefficients (s₁ := { env := [], heap := { cells := [a.value, a.value] } })
  all_goals
    simp [Runtime.eval, Runtime.readRef, Runtime.cellAt, Runtime.checkWritable,
      Runtime.writeRef, Runtime.liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

open Lean Elab Command in
run_cmd do
  let names := [``KernelPolynomial.weightedSum_insert, ``KernelPolynomial.weightedSum_normalize,
    ``KernelPolynomial.weightedSum_append, ``KernelPolynomial.weightedSum_add,
    ``KernelPolynomial.weightedSum_neg, ``KernelPolynomial.weightedSum_sub,
    ``KernelPolynomial.weightedSum_mul, ``coeff_normalize, ``normalize_equivalent,
    ``coeff_add, ``coeff_sub, ``coeff_mul, ``productCoefficient_normalize_left,
    ``productCoefficient_normalize_right, ``normalized_coefficients,
    ``eval_add_coefficients, ``eval_sub_coefficients, ``eval_mul_coefficients,
    ``successful_add_coefficients, ``successful_sub_coefficients, ``successful_mul_coefficients,
    ``runtime_add_coefficients, ``runtime_sub_coefficients, ``runtime_mul_coefficients,
    ``successful_add_equivalent, ``successful_sub_equivalent, ``successful_mul_equivalent,
    ``move_balance_coefficients, ``cancel_balance_coefficients,
    ``product_all_coefficients, ``product_equivalent, ``product_represents,
    ``source_coefficients, ``effectful_coefficients]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"COEFFICIENT_ARITHMETIC_COMPLETE: {names.length} theorem dependency audits"

end Macaulean.M2.Verification.PolynomialArithmetic.CoefficientTests
