import MacauleanTest.PolynomialCases
import MacauleanTest.GroebnerChecks
import Macaulean.Interpreter.Session
import Macaulean.Interpreter.Check

/-! Kernel examples and pure snapshot tests for the actual source runtime.
No native_decide, added axioms, or proof holes are used. These establish concrete
execution results and representation laws, not a universal Buchberger theorem. -/
namespace Macaulean.M2.GroebnerKernelTests
open Algebra PolynomialCases
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

example : run "rr=QQ[px,py];listForm ((px+py)^2-px^2-2*px*py-py^2)" =
    .ok (.list []) := by decide +kernel
example : run "rr=QQ[px,py];listForm (px/2+py/3)" =
    .ok (form [([1,0],mkRat 1 2),([0,1],mkRat 1 3)]) := by decide +kernel
example : run "rr=QQ[px];old=px;ss=QQ[px];old+px" =
    .error .differentRings := by decide +kernel
example : run "rr=QQ[px];listForm ((gens gb ideal(2*px))_(0,0))" =
    .ok (form [([1],1)]) := by decide +kernel
example : run "rr=QQ[px];ii=ideal(2*px);gg=gb ii;gens ii*getChangeMatrix gg==gens gg" =
    .ok (.bool true) := by decide +kernel
example : runWithFuel 2 "rr=QQ[px];gb ideal(px^2-1)" =
    .error .fuelExhausted := by decide +kernel
example : (Value.ofWire ["PolynomialRing","0","x"]).isOk = false := by decide +kernel
example : (Value.ofWire ["GroebnerBasis","0"]).isOk = false := by decide +kernel

theorem fixed_exponent_dimension (p : Poly) (t : Macaulean.PolyTerm Rat p.ring.names.length) :
    t.monomial.powers.length = p.ring.names.length := t.monomial.powers_length

theorem scalar_promotion (r : Algebra.Ring) (n : Int) :
    promotePolynomial r (.zz n) = .ok (Poly.constant r n) := rfl

theorem rational_promotion (r : Algebra.Ring) (q : Rat) :
    promotePolynomial r (.qq q) = .ok (Poly.constant r q) := rfl

theorem reject_foreign_promotion (r : Algebra.Ring) (p : Poly) (h : p.ring ≠ r) :
    promotePolynomial r (.polynomial p) = .error .differentRings := by
  simp [promotePolynomial,h]

theorem bad_dimension_rejected (r : Algebra.Ring) (powers : List Nat) (c : Rat)
    (h : powers.length ≠ r.names.length) :
    Poly.ofTerms r [(powers,c)] = none := by
  simp [Poly.ofTerms,h]

theorem normalized_wrapper (r : Algebra.Ring) (p : Macaulean.Polynomial Rat r.names.length) :
    (Poly.ofData r p).data = p.normalize := rfl

theorem source_gb_alias : Library.lookup "gb" = Library.lookup "m2gbMain" := by rfl

theorem failed_input_preserves_ring_counter (s : Session) (t : Term) (fuel : Nat) (e : Error)
    (h : s.evaluate t fuel = .error e) :
    (s.step t false fuel).session.heap.nextRing = s.heap.nextRing := by
  simp [Session.step,h]

private def execute (s : Session) (source : String) (fuel := Runtime.defaultFuel) : Except String Session.Result := do
  let t ← parse source
  return s.step t false fuel

open Lean Elab Command in
run_cmd do
  let .ok initial := execute {} "rr=QQ[x];old=x;g=gb ideal(x^2-1)"
    | throwError "snapshot setup failed"
  let .ok _ := initial.outcome | throwError "snapshot setup did not execute"
  let original := initial.session
  let .ok changed := execute original "ss=QQ[x];x"
    | throwError "ring fork failed"
  let .ok _ := changed.outcome | throwError "ring fork did not execute"
  let .ok failed := execute original "ss=QQ[x];1/0"
    | throwError "error test did not parse"
  unless failed.outcome == .error .divByZero do throwError "missing expected error"
  unless failed.session.heap.nextRing == original.heap.nextRing &&
      failed.session.lookup "x" == original.lookup "x" do
    throwError "failed input leaked new ring identity or variable binding"
  unless changed.session.heap.nextRing == original.heap.nextRing+1 do
    throwError "successful ring fork did not allocate a fresh identity"
  for s in [original,failed.session] do
    let .ok result := execute s "(old^2-1)%g" | throwError "snapshot replay failed"
    let .ok (.polynomial p) := result.outcome | throwError "snapshot result is not a polynomial"
    unless p.isZero do throwError "old basis changed after editing a later ring"
  let .ok exhausted := execute original "gb ideal(x^3-1,x^2-1)" 3
    | throwError "depth test did not parse"
  unless exhausted.outcome == .error .fuelExhausted &&
      exhausted.session.heap.cells.length == original.heap.cells.length &&
      exhausted.session.heap.nextRing == original.heap.nextRing do
    throwError "exhaustion published a partial basis or heap mutation"

-- Exercise the actual theorem-registration path, including dependent polynomial
-- data reification, rather than testing only a pretty-printer.
open Lean Elab Command in
run_cmd do
  let source := "rr=QQ[px];px^2+1"
  let result := run source
  match result with
  | .ok (.polynomial _) => pure ()
  | _ => throwError "certificate source did not produce a polynomial"
  addRunTheorem `GroebnerKernelTests.polynomialCertificate source result
    "Kernel-checked polynomial execution; no foreign ring identity is trusted."
end Macaulean.M2.GroebnerKernelTests
