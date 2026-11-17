import Macaulean.Interpreter.GCD.Reduction

namespace Macaulean.M2.GCD.Execution
open Macaulean.M2.Runtime Univariate

/-- Bindings used by the source reduction routine. -/
structure ReductionGlobals (s : State) : Prop where
  reducer : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer"))
  reduce : s.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce"))
  row : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow"))
  coefficient : s.env.lookup "leadCoefficient" = some (.algebra (.builtin .leadCoefficient))
  monomial : s.env.lookup "leadMonomial" = some (.algebra (.builtin .leadMonomial))
  term : s.env.lookup "leadTerm" = some (.algebra (.builtin .leadTerm))
  divides : s.env.lookup "m2MonomialDivides" = some (.algebra (.builtin .monomialDivides))
  quotient : s.env.lookup "m2MonomialQuotient" = some (.algebra (.builtin .monomialQuotient))

theorem ReductionGlobals.of_extends {s t : State} (h : ReductionGlobals s)
    (he : Extends s t) : ReductionGlobals t := by
  constructor <;> simp only [he.env]
  · exact h.reducer
  · exact h.reduce
  · exact h.row
  · exact h.coefficient
  · exact h.monomial
  · exact h.term
  · exact h.divides
  · exact h.quotient

def reductionArgs (id : Nat) (name : String) (p g r : Poly) : Value :=
  .sequence [value id name p,.list [],singletonDivisor id name g,value id name r]

theorem cancellation_step (fuel id : Nat) (name : String) (s : State)
    (t u : Univariate.Term) (ts us : List Univariate.Term) (r : Poly)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us))
    (hd : u.monomial.degree ≤ t.monomial.degree) (globals : ReductionGlobals s) :
    ∃ next, Extends s next ∧
      ∀ result after,
        call (fuel+33) (.algebra (.library "m2gbReduce"))
          (reductionArgs id name
            (KernelPolynomial.sub ⟨t :: ts⟩
              (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)) ⟨u :: us⟩ r) next =
            .ok (result,after) →
        call (fuel+40) (.algebra (.library "m2gbReduce"))
          (reductionArgs id name ⟨t :: ts⟩ ⟨u :: us⟩ r) s = .ok (result,after) := by
  let vs := reductionLocals (value id name ⟨t :: ts⟩) (.list [])
    (singletonDivisor id name ⟨u :: us⟩) (value id name r)
  let entered := (s.allocate vs).2
  let selectorArgs := [value id name ⟨t :: ts⟩,singletonDivisor id name ⟨u :: us⟩,Value.zz 0]
  let selected := (entered.allocate selectorArgs).2
  have he : Extends entered selected := allocate_extends entered selectorArgs
  have hframe := (allocated_frame s vs).after_call he
  obtain ⟨s4, hw4, hf4⟩ := hframe.write 4 (.zz 0) (by simp [vs, reductionLocals])
  obtain ⟨s6, hw6, hf6⟩ := hf4.write 6 (.list [value id name ⟨u :: us⟩,.list []])
    (by simp [vs, reductionLocals])
  obtain ⟨s7, hw7, hf7⟩ := hf6.write 7 (value id name (cancellationTerm t u))
    (by simp [vs, reductionLocals])
  let next := emptyRowAfter s7 (value id name (cancellationTerm t u))
  have hn : Extends s next :=
    hf7.extends.trans (allocate_extends s7 [.list [],value id name (cancellationTerm t u),.list [],.zz 0])
  refine ⟨next, hn, ?_⟩
  intro result after hrec
  have hselector := reducer_divides (fuel+15) id name entered t u ts us hp hg hd
    globals.monomial globals.divides
  have hbranch := reduction_cancel (fuel+6) id name s s4 s6 s7 after t u ts us
    (value id name r) .null .null .null result hp hg hd hf4
    globals.coefficient globals.monomial globals.quotient globals.row globals.reduce
    hw6 hw7 (by simpa [Nat.add_assoc, reductionArgs, next] using hrec)
  apply reduction_dispatch fuel id name s selected s4 after t ts (.list [])
    (singletonDivisor id name ⟨u :: us⟩) (value id name r) (.zz 0) result false hp
    globals.reducer
  · simpa [Nat.add_assoc, vs, entered, selected, selectorArgs] using hselector
  · exact he
  · exact hw4
  · decide +kernel
  · simpa [Nat.add_assoc] using hbranch

theorem move_head_step (fuel id : Nat) (name : String) (s : State)
    (t u : Univariate.Term) (ts us : List Univariate.Term) (r : Poly)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us)) (hr : Canonical r.terms)
    (hd : ¬ u.monomial.degree ≤ t.monomial.degree) (globals : ReductionGlobals s) :
    ∃ next, Extends s next ∧
      ∀ result after,
        call (fuel+34) (.algebra (.library "m2gbReduce"))
          (reductionArgs id name ⟨ts⟩ ⟨u :: us⟩ (KernelPolynomial.add r ⟨[t]⟩)) next =
            .ok (result,after) →
        call (fuel+40) (.algebra (.library "m2gbReduce"))
          (reductionArgs id name ⟨t :: ts⟩ ⟨u :: us⟩ r) s = .ok (result,after) := by
  let vs := reductionLocals (value id name ⟨t :: ts⟩) (.list [])
    (singletonDivisor id name ⟨u :: us⟩) (value id name r)
  let entered := (s.allocate vs).2
  let selectorArgs := [value id name ⟨t :: ts⟩,singletonDivisor id name ⟨u :: us⟩,Value.zz 0]
  let selectorEndArgs := [value id name ⟨t :: ts⟩,singletonDivisor id name ⟨u :: us⟩,Value.zz 1]
  let selected := ((entered.allocate selectorArgs).2.allocate selectorEndArgs).2
  have he : Extends entered selected := (allocate_extends entered selectorArgs).trans
    (allocate_extends (entered.allocate selectorArgs).2 selectorEndArgs)
  have hframe := (allocated_frame s vs).after_call he
  obtain ⟨s4, hw4, hf4⟩ := hframe.write 4 (.zz (-1)) (by simp [vs, reductionLocals])
  obtain ⟨next, hw5, hf5⟩ := hf4.write 5 (value id name ⟨[t]⟩) (by simp [vs, reductionLocals])
  refine ⟨next, hf5.extends, ?_⟩
  intro result after hrec
  have hselector := reducer_not_divides (fuel+15) id name entered t u ts us hp hg hd
    globals.monomial globals.divides globals.reducer
  have hbranch := reduction_move_head (fuel+16) id name s s4 next after t ts r
    (.list []) (singletonDivisor id name ⟨u :: us⟩) (.zz (-1)) .null .null .null result
    hp hr hf4 globals.term globals.reduce hw5
    (by simpa [Nat.add_assoc, reductionArgs] using hrec)
  apply reduction_dispatch fuel id name s selected s4 after t ts (.list [])
    (singletonDivisor id name ⟨u :: us⟩) (value id name r) (.zz (-1)) result true hp
    globals.reducer
  · simpa [Nat.add_assoc, vs, entered, selected, selectorArgs, selectorEndArgs] using hselector
  · exact he
  · exact hw4
  · decide +kernel
  · simpa [Nat.add_assoc] using hbranch

end Macaulean.M2.GCD.Execution
