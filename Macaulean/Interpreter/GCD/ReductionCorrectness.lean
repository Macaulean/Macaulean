import Macaulean.Interpreter.GCD.ReductionTotal

namespace Macaulean.M2.GCD.Execution
open Univariate

private theorem add_below (p q : Poly) (bound : Nat)
    (hp : Below bound p.terms) (hq : Below bound q.terms) :
    Below bound (KernelPolynomial.add p q).terms := by
  apply normalize_below
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht
  · exact hq t ht

theorem ReductionTrace.degree_bound {g p r out : Poly} (trace : ReductionTrace g p r out)
    (hr : Below (rank g - 1) r.terms) : Below (rank g - 1) out.terms := by
  induction trace with
  | done r => exact hr
  | cancel t u ts us r out hg hd next ih => exact ih hr
  | move t u ts us r out hg hd next ih =>
    apply ih
    apply add_below _ _ _ hr
    apply (below_cons ..).mpr
    refine ⟨?_, below_nil _⟩
    rw [hg]
    change t.monomial.degree < (u.monomial.degree + 1) - 1
    omega

private theorem add_zero_left (p : Poly) (hp : Canonical p.terms) :
    KernelPolynomial.add ⟨[]⟩ p = p := by
  apply polynomial_ext (add_canonical ..) hp
  intro k
  rw [coeff_add, coeff_nil]
  exact Rat.zero_add _

private theorem add_zero_right (p : Poly) (hp : Canonical p.terms) :
    KernelPolynomial.add p ⟨[]⟩ = p := by
  apply polynomial_ext (add_canonical ..) hp
  intro k
  rw [coeff_add, coeff_nil]
  exact Rat.add_zero _

private theorem sub_add_reorder (p q r : Poly) :
    KernelPolynomial.add (KernelPolynomial.sub p q) r =
      KernelPolynomial.sub (KernelPolynomial.add p r) q := by
  apply polynomial_ext (add_canonical ..) (sub_canonical ..)
  intro k
  simp only [coeff_add, coeff_sub]
  grind

private theorem move_add (t : Univariate.Term) (ts : List Univariate.Term) (r : Poly) :
    KernelPolynomial.add ⟨ts⟩ (KernelPolynomial.add r ⟨[t]⟩) =
      KernelPolynomial.add ⟨t :: ts⟩ r := by
  apply polynomial_ext (add_canonical ..) (add_canonical ..)
  intro k
  simp only [coeff_add, coeff_cons, coeff_nil]
  grind

/-- Divisibility of the pending polynomial plus accumulator is the loop
invariant. This statement includes arbitrary polynomial divisor witnesses. -/
theorem ReductionTrace.common_divisors {g p r out : Poly}
    (trace : ReductionTrace g p r out) (hr : Canonical r.terms) (d : Poly) :
    (Divides d g ∧ Divides d out) ↔
      (Divides d g ∧ Divides d (KernelPolynomial.add p r)) := by
  induction trace with
  | done r => rw [add_zero_left r hr]
  | cancel t u ts us r out hg hd next ih =>
    rw [ih hr, sub_add_reorder]
    exact (common_divisors_sub _ g (cancellationTerm t u) d (add_canonical ..)).trans and_comm
  | move t u ts us r out hg hd next ih =>
    rw [ih (add_canonical ..), move_add]

/-- Starting with zero accumulator gives the two algebraic properties needed
by Euclid: a strictly smaller remainder and exactly the same common divisors. -/
theorem ReductionTrace.remainder_properties {u : Univariate.Term}
    {us : List Univariate.Term} {p out : Poly}
    (trace : ReductionTrace ⟨u :: us⟩ p ⟨[]⟩ out) (hp : Canonical p.terms) :
    Below u.monomial.degree out.terms ∧
      ∀ d, (Divides d ⟨u :: us⟩ ∧ Divides d out) ↔
        (Divides d p ∧ Divides d ⟨u :: us⟩) := by
  constructor
  · simpa only [rank, Nat.add_sub_cancel] using trace.degree_bound (below_nil _)
  · intro d
    have h := trace.common_divisors .nil d
    rw [add_zero_right p hp] at h
    exact h.trans and_comm

/-- Total correctness for the source reduction call used inside normal form.
This includes successful execution, not merely a postcondition on success. -/
theorem reduction_correct (id : Nat) (name : String)
    (p : Poly) (u : Univariate.Term) (us : List Univariate.Term)
    (hp : Canonical p.terms) (hg : Canonical (u :: us))
    (s : Runtime.State) (globals : ReductionGlobals s)
    (budget : Nat) (hb : 64 * (rank p+1) ≤ budget) :
    ∃ out after, Canonical out.terms ∧ Extends s after ∧
      Below u.monomial.degree out.terms ∧
      (∀ d, (Divides d ⟨u :: us⟩ ∧ Divides d out) ↔
        (Divides d p ∧ Divides d ⟨u :: us⟩)) ∧
      Runtime.call budget (.algebra (.library "m2gbReduce"))
        (reductionArgs id name p ⟨u :: us⟩ ⟨[]⟩) s =
        .ok (.list [value id name out,.list []],after) := by
  obtain ⟨out,after,ho,he,trace,run⟩ := reduction_total id name u us hg
    (rank p) p ⟨[]⟩ hp .nil rfl s globals budget hb
  obtain ⟨hdegree,hdiv⟩ := trace.remainder_properties hp
  exact ⟨out,after,ho,he,hdegree,hdiv,run⟩

end Macaulean.M2.GCD.Execution
