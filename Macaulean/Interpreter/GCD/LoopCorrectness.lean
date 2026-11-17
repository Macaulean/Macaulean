import Macaulean.Interpreter.GCD.NormalForm
import Macaulean.Interpreter.GCD.TotalCorrectness

namespace Macaulean.M2.GCD.Execution
open Macaulean.M2.Runtime Univariate

structure GCDGlobals (s : State) : Prop extends NormalFormGlobals s where
  normalForm : s.env.lookup "normalForm" = some (.algebra (.library "normalForm"))
  loop : s.env.lookup "m2gcdLoop" = some (.algebra (.library "m2gcdLoop"))

theorem GCDGlobals.of_extends {s t : State} (h : GCDGlobals s)
    (he : Extends s t) : GCDGlobals t := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨h.toReductionGlobals.of_extends he, ?_, ?_, ?_, ?_⟩
    · simpa only [he.env] using h.data
    · simpa only [he.env] using h.ring
    · simpa only [he.env] using h.promote
    · simpa only [he.env] using h.bare
  · simpa only [he.env] using h.normalForm
  · simpa only [he.env] using h.loop

theorem monic_gcd_zero (p : Poly) (hp : Canonical p.terms) :
    TotalCorrectness.IsGCD Divides p ⟨[]⟩ (monicNormalize p) := by
  refine ⟨(monicNormalize_divides p p hp).mpr (divides_self p hp),
    divides_zero _, ?_⟩
  intro c hc _
  exact (divides_monicNormalize c p hp).mpr hc

/-- Total correctness of the actual source Euclidean loop. A fixed bound `n`
on both input ranks is retained during induction on the second input's rank. -/
theorem gcd_loop_total (id : Nat) (name : String) (n : Nat) :
    ∀ k (p g : Poly), rank g = k →
    Canonical p.terms → Canonical g.terms → rank p ≤ n → rank g ≤ n →
    ∀ (s : State), GCDGlobals s →
    ∀ budget, 64 * (n+1) + 8*k + 200 ≤ budget →
      ∃ out after, Canonical out.terms ∧ MonicOrZero out ∧
        TotalCorrectness.IsGCD Divides p g out ∧ Extends s after ∧
        call budget (.algebra (.library "m2gcdLoop"))
          (.sequence [value id name p,value id name g]) s =
          .ok (value id name out,after) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro p g hk hp hg hpn hgn s globals budget hb
    cases g with
    | mk gs =>
      cases gs with
      | nil =>
        let after := (s.allocate [value id name p,value id name ⟨[]⟩]).2
        refine ⟨monicNormalize p,after,monicNormalize_canonical p hp,
          monicNormalize_monic p hp,monic_gcd_zero p hp,allocate_extends s _,?_⟩
        have hbudget : budget-10+10 = budget := by omega
        cases p with
        | mk ps =>
          cases ps with
          | nil =>
            simpa only [hbudget, monicNormalize] using gcd_both_zero (budget-10) id name s
          | cons t ts =>
            simpa only [hbudget] using gcd_second_zero (budget-10) id name s t ts hp globals.coefficient
      | cons u us =>
        let entered := (s.allocate [value id name p,value id name ⟨u :: us⟩]).2
        have he := allocate_extends s [value id name p,value id name ⟨u :: us⟩]
        have ge := globals.of_extends he
        have hnfbound : 64 * (rank p+1) ≤ (budget-107)+94 := by omega
        obtain ⟨r, next, hr, hen, hdegree, hdiv, hnf⟩ :=
          normal_form_correct (budget-107) id name p u us hp hg entered ge.toNormalFormGlobals hnfbound
        have hlt : rank r < k := by
          have h := rank_le_of_below hdegree
          change u.monomial.degree+1 = k at hk
          omega
        have hrn : rank r ≤ n := by omega
        have hbudget : 64 * (n+1) + 8*rank r + 200 ≤ budget-3 := by omega
        obtain ⟨out,after,ho,hm,hgcd,hea,hrec⟩ := ih (rank r) hlt ⟨u :: us⟩ r rfl hg hr
          hgn hrn next (ge.of_extends hen) (budget-3) hbudget
        refine ⟨out,after,ho,hm,?_,he.trans (hen.trans hea),?_⟩
        · obtain ⟨hgo,hro,hcommon⟩ := hgcd
          obtain ⟨hpo,hgo⟩ := (hdiv out).mp ⟨hgo,hro⟩
          refine ⟨hpo,hgo,?_⟩
          intro c hcp hcg
          obtain ⟨hcg,hcr⟩ := (hdiv c).mpr ⟨hcp,hcg⟩
          exact hcommon c hcg hcr
        · have h20 : budget-20+20 = budget := by omega
          have h13 : budget-20+13 = budget-107+100 := by omega
          have h17 : budget-20+17 = budget-3 := by omega
          rw [← h20]
          apply gcd_step (budget-20) id name s next after p u us hg
            (value id name r) (value id name out) globals.normalForm globals.loop
          · simpa only [h13] using hnf
          · simpa only [h17] using hrec

end Macaulean.M2.GCD.Execution
