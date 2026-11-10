import Macaulean.Verification.ReductionRepresentation

namespace Macaulean.M2.Verification.ReductionRepresentation.Tests
open Views ProofJobs.RuntimeReduction
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

-- This is exactly the original generic target, with no extra mathematical
-- hypotheses or restricted dimensions hidden in the theorem application.
example : RepresentationStatement := representation

private def ring : Polynomials.RingInfo := ⟨19,["x","y"]⟩
private def term (c : Rat) (x y : Nat) : Macaulean.PolyTerm Rat 2 := ⟨c,⟨[x,y],rfl⟩⟩
private def poly (ts : List (Macaulean.PolyTerm Rat 2)) : Views.Polynomial ring := ⟨⟨ts⟩⟩
private def zero := poly []
private def one := poly [term 1 0 0]
private def x := poly [term 1 1 0]
private def y := poly [term 1 0 1]
private def xx := poly [term 1 2 0]
private def xxx := poly [term 1 3 0]
private def row (a b : Views.Polynomial ring) : Row ring 2 := ⟨[a,b],rfl⟩
private def reducers : List (RepresentedReducer ring 2) :=
  [⟨xxx,row x zero⟩,⟨xx,row one zero⟩]
private def pending := poly [term 2 2 0,term (-1) 2 0,term 1 0 1,term 0 3 3]
private def initial : Runtime.State := { heap := { cells := [.zz 99] } }

-- Noncanonical input, two variables, two-dimensional rows, an initial skipped
-- reducer, cancellation of x², then movement of y into the remainder.
example : (Runtime.call 200 (.algebra (.library "m2gbReduce"))
    (.sequence [pending.value,(row one one).value,
      .list (reducers.map RepresentedReducer.value),zero.value]) initial).toOption.map
    (fun (v,s) => (v,s.heap.cells.take 1)) =
    some (.list [y.value,(row zero one).value],[.zz 99]) := by decide +kernel

-- A zero reducer can cause a runtime error; the universal theorem deliberately
-- proves successful-return correctness without assuming totality.
example : (Runtime.call 100 (.algebra (.library "m2gbReduce"))
    (.sequence [pending.value,(row one one).value,
      .list [(RepresentedReducer.mk zero (row zero zero)).value],zero.value]) initial).toOption.isNone =
    true := by decide +kernel

open Lean Elab Command in
run_cmd do
  for dependency in ← Lean.collectAxioms ``representation do
    unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
      throwError "representation depends on unapproved axiom {dependency}"
  logInfo "REDUCTION_REPRESENTATION_COMPLETE: exact universal target, mixed branch regression, axiom audit"

end Macaulean.M2.Verification.ReductionRepresentation.Tests
