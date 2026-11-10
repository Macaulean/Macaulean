import Macaulean.Verification.ReductionIrreducibility

namespace Macaulean.M2.Verification.ReductionIrreducibility.Tests
open Views ProofJobs.RuntimeReduction
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- No extra canonicality, representation, nonzero-reducer or termination premise.
theorem exact_target : IrreducibleStatement := irreducible

private def ring : Polynomials.RingInfo := ⟨23,["x","y"]⟩
private def term (c : Rat) (x y : Nat) : Macaulean.PolyTerm Rat 2 := ⟨c,⟨[x,y],rfl⟩⟩
private def poly (ts : List (Macaulean.PolyTerm Rat 2)) : Views.Polynomial ring := ⟨⟨ts⟩⟩
private def zero := poly []
private def one := poly [term 1 0 0]
private def x := poly [term 1 1 0]
private def xx := poly [term 1 2 0]
private def y := poly [term 1 0 1]
private def row (p : Views.Polynomial ring) : Row ring 1 := ⟨[p],rfl⟩
private def reducer (p : Views.Polynomial ring) : RepresentedReducer ring 1 := ⟨p,row one⟩
private def initial : Runtime.State := { heap := { cells := [.zz 99] } }

-- The selector must reject both distinct heads, then return -1.
theorem all_rejected : (Runtime.call 100 (.algebra (.library "m2gbReducer"))
    (.sequence [y.value,.list [(reducer xx).value,(reducer x).value],.zz 0]) initial).toOption.map
    (fun (v,s) => (v,s.heap.cells.take 1)) = some (.zz (-1),[.zz 99]) := by decide +kernel

-- A rejection of the first candidate does not justify moving the pending head:
-- the second candidate divides it, and source order chooses that index.
theorem later_divisor : (Runtime.call 100 (.algebra (.library "m2gbReducer"))
    (.sequence [x.value,.list [(reducer xx).value,(reducer x).value],.zz 0]) initial).toOption.map
    Prod.fst = some (.zz 1) := by decide +kernel

-- Nonzero initial remainder, noncanonical pending terms, no representation
-- invariant for the zero input row. Cancellation and movement still leave y+1.
private def pending := poly [term 2 2 0,term (-1) 2 0,term 1 0 1,term 0 3 3]
private def expected := poly [term 1 0 1,term 1 0 0]
private def minusX := poly [term (-1) 1 0]
theorem mixed_branches : (Runtime.call 200 (.algebra (.library "m2gbReduce"))
    (.sequence [pending.value,(row zero).value,.list [(reducer x).value],one.value]) initial).toOption.map
    (fun (v,s) => (v,s.heap.cells.take 1)) =
    some (.list [expected.value,(row minusX).value],[.zz 99]) := by decide +kernel

-- Empty reducers move every term; a zero reducer still reports an error.
theorem empty_reducers : (Runtime.call 100 (.algebra (.library "m2gbReduce"))
    (.sequence [y.value,(row zero).value,.list [],one.value]) initial).toOption.map Prod.fst =
    some (.list [expected.value,(row zero).value]) := by decide +kernel

theorem zero_reducer_error : (Runtime.call 100 (.algebra (.library "m2gbReducer"))
    (.sequence [x.value,.list [(reducer zero).value],.zz 0]) initial).toOption.isNone = true := by
  decide +kernel

-- The primitive bridge follows normalization and sums duplicate terms.
theorem noncanonical_rejected : ReducerSelection.test
    (poly [term 2 0 1,term (-1) 0 1,term 0 4 4]) x = .ok (.bool false) := by decide +kernel

open Lean Elab Command in
run_cmd do
  for theoremName in [``exact_target, ``ReducerSelection.negative,
      ``ReducerSelection.test_false, ``ReducerSelection.negative_leading_term,
      ``IrreducibleArithmetic.add, ``IrreducibleArithmetic.leading_term,
      ``ReductionMove.successful_step, ``ReductionCancel.successful_step,
      ``ReductionDispatch.successful_selected] do
    for dependency in ← Lean.collectAxioms theoremName do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{theoremName} depends on unapproved axiom {dependency}"
  logInfo "REDUCTION_IRREDUCIBILITY_COMPLETE: exact universal target, source selector and branch laws, nine axiom audits"

end Macaulean.M2.Verification.ReductionIrreducibility.Tests
