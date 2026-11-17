import Macaulean.Interpreter.GCD.ReductionSteps

namespace Macaulean.M2.GCD.Execution
open Macaulean.M2.Runtime Univariate

/-- A mathematical record of the branches taken by the actual reduction.
The execution theorem below constructs this record together with the result. -/
inductive ReductionTrace (g : Poly) : Poly → Poly → Poly → Prop where
  | done (r : Poly) : ReductionTrace g ⟨[]⟩ r r
  | cancel (t u : Univariate.Term) (ts us : List Univariate.Term) (r out : Poly)
      (hg : g = ⟨u :: us⟩) (hd : u.monomial.degree ≤ t.monomial.degree)
      (next : ReductionTrace g
        (KernelPolynomial.sub ⟨t :: ts⟩ (KernelPolynomial.mul (cancellationTerm t u) g)) r out) :
      ReductionTrace g ⟨t :: ts⟩ r out
  | move (t u : Univariate.Term) (ts us : List Univariate.Term) (r out : Poly)
      (hg : g = ⟨u :: us⟩) (hd : ¬ u.monomial.degree ≤ t.monomial.degree)
      (next : ReductionTrace g ⟨ts⟩ (KernelPolynomial.add r ⟨[t]⟩) out) :
      ReductionTrace g ⟨t :: ts⟩ r out

/-- Total execution of the checked-in reduction source for a nonzero singleton
divisor. The bound measures evaluator depth, including source helper calls. -/
theorem reduction_total (id : Nat) (name : String)
    (u : Univariate.Term) (us : List Univariate.Term) (hg : Canonical (u :: us)) :
    ∀ k (p r : Poly), Canonical p.terms → Canonical r.terms → rank p = k →
    ∀ (s : State), ReductionGlobals s →
    ∀ budget, 64 * (k+1) ≤ budget →
      ∃ out after, Canonical out.terms ∧ Extends s after ∧
        ReductionTrace ⟨u :: us⟩ p r out ∧
        call budget (.algebra (.library "m2gbReduce"))
          (reductionArgs id name p ⟨u :: us⟩ r) s =
            .ok (.list [value id name out,.list []],after) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro p r hp hr hk s globals budget hb
    cases p with
    | mk ps =>
      cases ps with
      | nil =>
        let vs := reductionLocals (value id name ⟨[]⟩) (.list [])
          (singletonDivisor id name ⟨u :: us⟩) (value id name r)
        refine ⟨r, (s.allocate vs).2, hr, allocate_extends s vs, .done r, ?_⟩
        have hex := reduction_zero (budget-10) id name (.list [])
          (singletonDivisor id name ⟨u :: us⟩) (value id name r) s
        have heq : budget-10+10 = budget := by omega
        simpa only [heq, reductionArgs] using hex
      | cons t ts =>
        have hpositive : 0 < k := by
          change t.monomial.degree + 1 = k at hk
          omega
        let fuel := budget-40
        have heq : fuel+40 = budget := by dsimp [fuel]; omega
        by_cases hd : u.monomial.degree ≤ t.monomial.degree
        · let q := KernelPolynomial.sub ⟨t :: ts⟩
            (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)
          have hq : Canonical q.terms := sub_canonical ..
          have hlt : rank q < k := by
            rw [← hk]
            exact cancellation_rank_lt hp hg hd
          obtain ⟨next, he, step⟩ := cancellation_step fuel id name s t u ts us r hp hg hd globals
          have hbudget : 64 * (rank q+1) ≤ fuel+33 := by dsimp [fuel]; omega
          obtain ⟨out, after, ho, ha, trace, run⟩ := ih (rank q) hlt q r hq hr rfl
            next (globals.of_extends he) (fuel+33) hbudget
          refine ⟨out,after,ho,he.trans ha,?_,?_⟩
          · exact .cancel t u ts us r out rfl hd trace
          · rw [← heq]
            exact step _ _ run
        · have htail : Canonical ts := by cases hp; assumption
          have hlt : rank (⟨ts⟩ : Poly) < k := by
            have h := sub_head_rank_lt hp
            rw [sub_head hp, hk] at h
            exact h
          obtain ⟨next, he, step⟩ := move_head_step fuel id name s t u ts us r hp hg hr hd globals
          have hbudget : 64 * (rank (⟨ts⟩ : Poly)+1) ≤ fuel+34 := by dsimp [fuel]; omega
          obtain ⟨out, after, ho, ha, trace, run⟩ := ih (rank (⟨ts⟩ : Poly)) hlt ⟨ts⟩
            (KernelPolynomial.add r ⟨[t]⟩) htail (add_canonical ..) rfl
            next (globals.of_extends he) (fuel+34) hbudget
          refine ⟨out,after,ho,he.trans ha,?_,?_⟩
          · exact .move t u ts us r out rfl hd trace
          · rw [← heq]
            exact step _ _ run

end Macaulean.M2.GCD.Execution
