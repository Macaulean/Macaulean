import Macaulean.Verification.PolynomialArithmetic
import Macaulean.Interpreter.Run

/-! Kernel-checked use sites for the arithmetic/lexical-runtime bridge. -/
namespace Macaulean.M2.Verification.PolynomialArithmetic.Tests
open Views
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private def ring : Polynomials.RingInfo := ⟨0, ["x"]⟩
private def poly (terms : List (Rat × Nat)) : Views.Polynomial ring :=
  ⟨⟨terms.map fun (c, k) => ⟨c, ⟨[k], rfl⟩⟩⟩⟩

-- Unsorted inputs, cancellation, explicit zero terms and rational duplicates.
private def messy : Views.Polynomial ring :=
  poly [(-3,0), (0,5), (1/2,1), (3,0), (1/2,1)]
private def divisor := poly [(1,1), (-1,0)]
private def product := poly [(1,2), (-1,1)]

private theorem product_execution :
    evalBinOp .mul messy.value divisor.value = .ok product.value := by decide +kernel

theorem noncanonical_product (ctx : Context) :
    denote ctx product = denote ctx messy * denote ctx divisor :=
  successful_mul messy divisor product product_execution ctx

-- The no-divisor and divisor branch arithmetic, including a nonzero remainder.
example (ctx : Context) :
    denote ctx (poly [(1,0)]) + denote ctx (poly [(1,2), (3,0)]) =
      denote ctx (poly [(1,2), (1,0)]) + denote ctx (poly [(3,0)]) := by
  apply move_balance (term := poly [(1,2)]) <;> decide +kernel

example (ctx : Context) :
    denote ctx (poly [(1,1)]) + denote ctx (poly [(3,0)]) =
      (denote ctx (poly [(1,2)]) + denote ctx (poly [(3,0)])) -
        denote ctx (poly [(1,1)]) * denote ctx divisor := by
  apply cancel_balance (product := product) <;> decide +kernel

-- Zero-variable rings and cancellation to the zero polynomial are admitted.
private def constants : Polynomials.RingInfo := ⟨1, []⟩
private def constant (c : Rat) : Views.Polynomial constants := ⟨⟨[⟨c, ⟨[], rfl⟩⟩]⟩⟩
example (ctx : Context) : denote ctx (constant 6) = denote ctx (constant 2) * denote ctx (constant 3) :=
  successful_mul (constant 2) (constant 3) (constant 6) (by decide +kernel) ctx
example (ctx : Context) : denote ctx (⟨⟨[]⟩⟩ : Views.Polynomial ring) =
    denote ctx messy - denote ctx messy :=
  successful_sub messy messy ⟨⟨[]⟩⟩ (by decide +kernel) ctx

-- A theorem about parsed source plus its mathematical identity at every
-- assignment. This remains a fixed-source certificate, not a parser theorem.
theorem source_identity :
    run "R=QQ[x];(x+1)*(x-1)" = .ok (poly [(1,2), (-1,0)]).value ∧
    ∀ ctx, denote ctx (poly [(1,2), (-1,0)]) =
      denote ctx (poly [(1,1), (1,0)]) * denote ctx divisor := by
  constructor
  · decide +kernel
  · exact successful_mul _ _ _ (by decide +kernel)

-- The right operand sees the left operand's write. The operator itself retains
-- that resulting state. The polynomial is arbitrary, not a fixed test value.
theorem effectful_operands (p : Views.Polynomial r) :
    let initial : Runtime.State := { env := [], heap := { cells := [.null, p.value] } }
    let after : Runtime.State := { env := [], heap := { cells := [p.value, p.value] } }
    ∃ out : Views.Polynomial r,
      Runtime.eval 3
        (.binop .mul (.set (.slot 0 0) (.read (.slot 0 1))) (.read (.slot 0 0)))
        [[0,1]] initial = .ok (out.value, after) ∧
      ∀ ctx, denote ctx out = denote ctx p * denote ctx p := by
  dsimp only
  apply runtime_mul (s₁ := { env := [], heap := { cells := [p.value, p.value] } })
  all_goals
    simp [Runtime.eval, Runtime.readRef, Runtime.cellAt, Runtime.checkWritable,
      Runtime.writeRef, Runtime.liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

-- Precise error boundaries: no foreign-ring or malformed value can be used as
-- a same-ring polynomial operand merely because its printed name agrees.
example : evalBinOp .mul (poly [(1,1)]).value
    (.algebra (.poly ⟨1,["x"]⟩ [(1,[1])])) =
      .error (.algebra "polynomials belong to different rings") := by decide +kernel
example : evalBinOp .add (poly [(1,1)]).value
    (.algebra (.poly ring [(1,[1,0])])) =
      .error (.algebra "polynomial exponent vector has the wrong dimension") := by decide +kernel

-- Audit transitive proof dependencies, including the imported polynomial laws.
-- A proof hole or native-evaluation axiom must fail this test even if it enters
-- through an existing dependency rather than one of these files.
open Lean Elab Command in
run_cmd do
  let names := [``KernelPolynomial.denote_normalize, ``KernelPolynomial.denote_add,
    ``KernelPolynomial.denote_sub, ``KernelPolynomial.denote_mul, ``KernelPolynomial.denote_pow,
    ``eval_add, ``eval_sub, ``eval_mul, ``runtime_binary, ``runtime_add, ``runtime_sub,
    ``runtime_mul, ``successful_add, ``successful_sub, ``successful_mul,
    ``move_balance, ``cancel_balance, ``source_identity, ``effectful_operands]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"POLYNOMIAL_ARITHMETIC_COMPLETE: {names.length} theorem dependency audits"

end Macaulean.M2.Verification.PolynomialArithmetic.Tests
