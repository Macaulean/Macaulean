import Macaulean.Verification.ReductionValues
import Macaulean.Verification.CallNormal

/-! Exact execution of the source move branch, with decreasing recursive fuel. -/
namespace Macaulean.M2.Verification.ReductionMove
open Lexical Macaulean.M2.Runtime GCD.Execution Views PolynomialArithmetic

/-- All operations before recursion are the production primitives/operators.
The equality includes errors, so it also supports successful-call inversion. -/
theorem execute (fuel : Nat) (parent s next : State)
    (pending remainder term nextPending nextRemainder : Views.Polynomial r)
    (row gs j oldTerm divisor coefficient : Value)
    (hf : InFrame parent
      [pending.value,row,gs,remainder.value,j,oldTerm,divisor,coefficient] s)
    (hlead : parent.env.lookup "leadTerm" = some (.algebra (.builtin .leadTerm)))
    (hrecurse : parent.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce")))
    (ht : Polynomials.callPrimitive .leadTerm pending.value = .ok term.value)
    (hp : evalBinOp .sub pending.value term.value = .ok nextPending.value)
    (hr : evalBinOp .add remainder.value term.value = .ok nextRemainder.value)
    (hw : writeRef (.slot 0 5) term.value [frame parent 8] s = .ok next) :
    eval (fuel+9) reductionMoveHead [frame parent 8] s =
      call (fuel+7) (.algebra (.library "m2gbReduce"))
        (.sequence [nextPending.value,row,gs,nextRemainder.value]) next := by
  have hn := hf.write_result 5 term.value (by simp) hw
  have h0 := hf.read 0 pending.value rfl
  have hn0 := hn.read 0 pending.value rfl
  have hn1 := hn.read 1 row rfl
  have hn2 := hn.read 2 gs rfl
  have hn3 := hn.read 3 remainder.value rfl
  have hn5 := hn.read 5 term.value rfl
  simp only [List.length_cons, List.length_nil, List.length_set] at h0 hn0 hn1 hn2 hn3 hn5
  have hl : readRef (.global "leadTerm") [frame parent 8] s =
      .ok (.algebra (.builtin .leadTerm)) := by simp [readRef, hf.env, hlead]
  have hc : readRef (.global "m2gbReduce") [frame parent 8] next =
      .ok (.algebra (.library "m2gbReduce")) := by simp [readRef, hn.env, hrecurse]
  simp only [reductionMoveHead, localVar, globalVar, eval, evalMany,
    checkWritable, h0, hn0, hn1, hn2, hn3, hn5, hl, hc,
    builtin_call _ _ _ _ _ ht, hw, hp, hr,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem exhausted (parent s next : State)
    (pending remainder term nextPending : Views.Polynomial r)
    (row gs j oldTerm divisor coefficient : Value)
    (hf : InFrame parent
      [pending.value,row,gs,remainder.value,j,oldTerm,divisor,coefficient] s)
    (hlead : parent.env.lookup "leadTerm" = some (.algebra (.builtin .leadTerm)))
    (hrecurse : parent.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce")))
    (ht : Polynomials.callPrimitive .leadTerm pending.value = .ok term.value)
    (hp : evalBinOp .sub pending.value term.value = .ok nextPending.value)
    (hw : writeRef (.slot 0 5) term.value [frame parent 8] s = .ok next) :
    eval 8 reductionMoveHead [frame parent 8] s = .error (.error .fuelExhausted) := by
  have hn := hf.write_result 5 term.value (by simp) hw
  have h0 := hf.read 0 pending.value rfl
  have hn0 := hn.read 0 pending.value rfl
  have hn1 := hn.read 1 row rfl
  have hn2 := hn.read 2 gs rfl
  have hn5 := hn.read 5 term.value rfl
  simp only [List.length_cons, List.length_nil, List.length_set] at h0 hn0 hn1 hn2 hn5
  have hl : readRef (.global "leadTerm") [frame parent 8] s =
      .ok (.algebra (.builtin .leadTerm)) := by simp [readRef, hf.env, hlead]
  have hc : readRef (.global "m2gbReduce") [frame parent 8] next =
      .ok (.algebra (.library "m2gbReduce")) := by simp [readRef, hn.env, hrecurse]
  simp only [reductionMoveHead, localVar, globalVar, eval, evalMany,
    checkWritable, h0, hn0, hn1, hn2, hn5, hl, hc,
    builtin_call _ _ _ _ _ ht, hw, hp,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- Invert a successful move branch at its original budget, preserving the
input representation invariant and protected bindings for the recursive call. -/
theorem successful (fuel : Nat) (parent s : State)
    (generators : Row r n) (pending remainder : Views.Polynomial r)
    (coefficients : Row r n) (gs j oldTerm divisor coefficient result : Value)
    (after : State)
    (hf : InFrame parent
      [pending.value,coefficients.value,gs,remainder.value,j,oldTerm,divisor,coefficient] s)
    (globals : PreludeBindings parent)
    (input : ProofJobs.RuntimeReduction.InputInvariant generators pending remainder coefficients)
    (success : catchReturn (eval fuel reductionMoveHead [frame parent 8] s) = .ok (result,after)) :
    ∃ (nextPending nextRemainder : Views.Polynomial r) (next : State) (depth : Nat),
      depth < fuel ∧ PreludeBindings next ∧
      ProofJobs.RuntimeReduction.InputInvariant generators nextPending nextRemainder coefficients ∧
      call depth (.algebra (.library "m2gbReduce"))
        (.sequence [nextPending.value,coefficients.value,gs,nextRemainder.value]) next =
          .ok (result,after) := by
  let term : Views.Polynomial r := ⟨⟨(KernelPolynomial.normalize pending.data).terms.take 1⟩⟩
  have ht : Polynomials.callPrimitive .leadTerm pending.value = .ok term.value :=
    ReductionValues.lead_term pending
  obtain ⟨np, hp, _⟩ := eval_sub_coefficients pending term
  obtain ⟨nr, hr, _⟩ := eval_add_coefficients remainder term
  obtain ⟨next, hw, hn⟩ := hf.write 5 term.value (by simp)
  have hl : parent.env.lookup "leadTerm" = some (.algebra (.builtin .leadTerm)) :=
    globals "leadTerm" (by decide)
  have hc : parent.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce")) :=
    globals "m2gbReduce" (by decide)
  have bound : 9 ≤ fuel := by
    by_cases low : fuel ≤ 8
    · exfalso
      have hm := Fuel.catchRefines (Fuel.eval_mono fuel (8-fuel) reductionMoveHead [frame parent 8] s)
      have hs := Fuel.preserves_success hm success
      have he := exhausted parent s next pending remainder term np coefficients.value gs j
        oldTerm divisor coefficient hf hl hc ht hp hw
      rw [Nat.add_sub_cancel' low, he] at hs
      cases hs
    · omega
  obtain ⟨extra, rfl⟩ : ∃ extra, fuel = extra+9 := ⟨fuel-9, by omega⟩
  rw [execute extra parent s next pending remainder term np nr coefficients.value gs j
    oldTerm divisor coefficient hf hl hc ht hp hr hw,
    (library_call_normal _ _ _ _).catchReturn_eq] at success
  refine ⟨np,nr,next,extra+7,by omega,?_,?_,success⟩
  · intro name protectedName
    rw [hn.env]
    exact globals name protectedName
  · intro powers
    exact (move_balance_coefficients pending remainder term np nr hp hr powers).trans (input powers)

end Macaulean.M2.Verification.ReductionMove
