import Macaulean.Verification.PolynomialRows

namespace Macaulean.M2.Verification.PolynomialRows.Tests
open Views
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private def ring : Polynomials.RingInfo := ⟨17,["x"]⟩
private def poly (ts : List (Rat × Nat)) : Views.Polynomial ring :=
  ⟨⟨ts.map fun (c,n) => ⟨c,⟨[n],rfl⟩⟩⟩⟩
private def initial : Runtime.State :=
  { env := [("m2gbSubtractRow", .algebra (.library "m2gbSubtractRow"))],
    heap := { cells := [.zz 99], nextRing := 18 } }

-- Noncanonical coefficients, cancellation, and rational scaling through the
-- actual library source, not a separate recursive implementation.
private def xs : Row ring 2 := ⟨[poly [(1,1),(2,1),(0,3)], poly [(1,0)]],rfl⟩
private def ys : Row ring 2 := ⟨[poly [(6,1)], poly [(4,0)]],rfl⟩
private def scale := poly [(1/2,0)]
private def output : Row ring 2 := ⟨[poly [], poly [(-1,0)]],rfl⟩

example : (Runtime.call 48 (.algebra (.library "m2gbSubtractRow"))
    (.sequence [xs.value,scale.value,ys.value,.zz 0]) initial).toOption.map Prod.fst =
      some output.value := by decide +kernel

-- The theorem includes empty rows and zero-variable rings, and does not need a
-- closed concrete runtime state or canonical polynomial terms.
example (r : Polynomials.RingInfo) (c : Views.Polynomial r)
    (s : Runtime.State)
    (h : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow"))) :
    ∃ (zs : Row r 0) (after : Runtime.State),
      Runtime.call 16 (.algebra (.library "m2gbSubtractRow"))
        (.sequence [(.list []),c.value,.list [],.zz 0]) s = .ok (zs.value,after) ∧
      Subtracts c [] [] zs.values ∧ RowProgram.AllocatesOnly s after :=
  execute c ⟨[],rfl⟩ ⟨[],rfl⟩ s 0 h

example : readRow ring 1 output.value = .error "coefficient-row view: wrong length" :=
  row_wrong_length output 1 (by decide)

open Lean Elab Command in
run_cmd do
  for name in [``construct, ``execute] do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"

end Macaulean.M2.Verification.PolynomialRows.Tests
