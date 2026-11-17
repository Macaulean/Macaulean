import Macaulean.Verification.RowRepresentation

namespace Macaulean.M2.Verification.PolynomialRows.Tests
open Views KernelPolynomial

-- Any pair of representations, in any ring and dimension, can be combined by
-- the actual library program. No canonical-form or generator-independence
-- assumption is needed.
theorem source_representation (c p q : Views.Polynomial r)
    (gs : List (Views.Polynomial r)) (xs ys : Row r gs.length)
    (hp : Represents p gs xs) (hq : Represents q gs ys)
    (s : Runtime.State)
    (global : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow"))) :
    ∃ (zs : Row r gs.length) (after : Runtime.State),
      Runtime.call (16*(gs.length+1)) (.algebra (.library "m2gbSubtractRow"))
        (.sequence [xs.value,c.value,ys.value,.zz 0]) s = .ok (zs.value,after) ∧
      Represents ⟨sub p.data (mul c.data q.data)⟩ gs zs ∧
      RowProgram.AllocatesOnly s after := by
  simpa only [Nat.zero_add] using execute_represents c p q gs xs ys hp hq s 0 global

private def ring : Polynomials.RingInfo := ⟨31,["x"]⟩
private def poly (ts : List (Rat × Nat)) : Views.Polynomial ring :=
  ⟨⟨ts.map fun (c,n) => ⟨c,⟨[n],rfl⟩⟩⟩⟩
private def messy := poly [(1/2,2),(3,0),(0,7),(-3,0),(1/2,2)]
private def clean := poly [(1,2)]

private theorem same : Equivalent messy clean := by
  intro powers
  simp only [Views.Polynomial.coeff, Views.Polynomial.raw, Polynomials.encode,
    messy, clean, poly, List.map_cons, List.map_nil, coefficient_cons, coefficient_nil]
  split <;> split <;> split <;> decide +kernel

-- Extensionality is stronger than evaluation at sample points: it preserves
-- every monomial weight, even for canceled and explicitly zero terms.
example (w : Macaulean.Mon ring.names.length → Rat) :
    weightedSum w messy.data.terms = weightedSum w clean.data.terms :=
  equivalent_weighted messy clean same w

-- Empty generator lists do not introduce a hidden nonempty-row assumption.
example (powers : List Nat) :
    (linearPolynomial ([] : List (Views.Polynomial ring)) []).coeff powers = 0 := rfl

open Lean Elab Command in
run_cmd do
  let names := [``mon_mul_assoc, ``weightedSum_weight_add, ``weightedSum_weight_scale,
    ``weightedSum_mul_assoc, ``weightedSum_split, ``weightedSum_vanish,
    ``weightedSum_ext, ``indicator_coefficient, ``equivalent_weighted,
    ``weightedSum_mul_add_right, ``linearPolynomial_coeff, ``Subtracts.weighted,
    ``Subtracts.represents, ``execute_represents, ``source_representation]
  for name in names do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"ROW_REPRESENTATION_COMPLETE: {names.length} theorem dependency audits"

end Macaulean.M2.Verification.PolynomialRows.Tests
