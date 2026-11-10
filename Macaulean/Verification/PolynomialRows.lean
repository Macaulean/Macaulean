import Macaulean.Verification.RowProgram
import Macaulean.Verification.PolynomialArithmetic

/-! Typed polynomial specialization of the executed coefficient-row update.
The dimension and coefficient guarantee apply to arbitrary same-ring rows,
including noncanonical sparse representations. -/
namespace Macaulean.M2.Verification.PolynomialRows
open Views

/-- Pointwise mathematical specification, independent of runtime operations. -/
inductive Subtracts (c : Views.Polynomial r) :
    List (Views.Polynomial r) → List (Views.Polynomial r) →
      List (Views.Polynomial r) → Prop where
  | nil : Subtracts c [] [] []
  | cons {x y z : Views.Polynomial r} {xs ys zs}
      (coeff : ∀ powers, z.coeff powers = x.coeff powers - productCoefficient c y powers)
      (tail : Subtracts c xs ys zs) : Subtracts c (x::xs) (y::ys) (z::zs)

theorem construct (c : Views.Polynomial r) (xs ys : List (Views.Polynomial r))
    (same : xs.length = ys.length) :
    ∃ zs, Subtracts c xs ys zs ∧
      RowProgram.Updates c.value (xs.map Views.Polynomial.value)
        (ys.map Views.Polynomial.value) (zs.map Views.Polynomial.value) := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.length_eq_zero_iff.mp (by simpa using same.symm)
    subst ys
    exact ⟨[], .nil, .nil⟩
  | cons x xs ih =>
    cases ys with
    | nil => simp at same
    | cons y ys =>
      obtain ⟨zs, spec, updates⟩ := ih ys (by simpa using same)
      obtain ⟨p, hm, hp⟩ := PolynomialArithmetic.eval_mul_coefficients c y
      obtain ⟨z, hs, hz⟩ := PolynomialArithmetic.eval_sub_coefficients x p
      exact ⟨z::zs, .cons (fun powers => by rw [hz, hp]) spec,
        .cons hm hs updates⟩

/-- The actual source helper terminates at a row-length-derived depth, returns
exactly the original dimension, and preserves every pre-existing runtime cell.
Only its fresh call frames are added to the heap. -/
theorem execute (c : Views.Polynomial r) (xs ys : Row r n)
    (s : Runtime.State) (spare : Nat)
    (global : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow"))) :
    ∃ (zs : Row r n) (after : Runtime.State),
      Runtime.call (spare + 16*(n+1)) (.algebra (.library "m2gbSubtractRow"))
        (.sequence [xs.value,c.value,ys.value,.zz 0]) s = .ok (zs.value,after) ∧
      Subtracts c xs.values ys.values zs.values ∧
      RowProgram.AllocatesOnly s after := by
  obtain ⟨zs, spec, updates⟩ := construct c xs.values ys.values
    (xs.size_eq.trans ys.size_eq.symm)
  have dim : zs.length = n := by
    have h := updates.lengths.2
    simpa [xs.size_eq] using h.symm
  obtain ⟨after, run, effects⟩ := RowProgram.execute updates s spare global
  refine ⟨⟨zs,dim⟩, after, ?_, spec, effects⟩
  simpa [RowProgram.arg, Row.value, dim] using run

end Macaulean.M2.Verification.PolynomialRows
