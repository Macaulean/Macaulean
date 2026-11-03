import Macaulean.Interpreter.GCD

/-!
# The Euclidean induction behind the GCD implementation

This module proves total correctness of the abstract Euclidean loop with an
explicit input-derived iteration bound. Its hypotheses describe the concrete
polynomial obligations. Source execution is proved separately in
`LoopCorrectness` and `ComputeCorrectness`, including the concrete algebraic
laws and the evaluator-depth bound for `Runtime.call` and `GCD.compute`.

The iteration budget here counts Euclidean calls; the DSL's depth budget also
has to cover polynomial reduction and expression evaluation.
-/
namespace Macaulean.M2.GCD.TotalCorrectness

structure Operations (α : Type) where
  zero : α
  remainder : α → α → α
  normalize : α → α
  /-- Zero has rank 0; a nonzero polynomial has rank degree + 1. -/
  rank : α → Nat

def IsGCD (divides : α → α → Prop) (f g d : α) : Prop :=
  divides d f ∧ divides d g ∧ ∀ c, divides c f → divides c g → divides c d

/-- Algebraic and descent obligations, not assumed global axioms. -/
structure Laws (ops : Operations α) (divides : α → α → Prop)
    (normalized : α → Prop) : Prop where
  divides_self : ∀ f, divides f f
  divides_zero : ∀ f, divides f ops.zero
  normalize_divides : ∀ f g, divides (ops.normalize f) g ↔ divides f g
  divides_normalize : ∀ f g, divides f (ops.normalize g) ↔ divides f g
  normalized_normalize : ∀ f, normalized (ops.normalize f)
  remainder_common : ∀ f g c, g ≠ ops.zero →
    (divides c g ∧ divides c (ops.remainder f g) ↔ divides c f ∧ divides c g)
  remainder_rank : ∀ f g, g ≠ ops.zero → ops.rank (ops.remainder f g) < ops.rank g

def loop [DecidableEq α] (ops : Operations α) : Nat → α → α → Option α
  | 0, _, _ => none
  | n+1, f, g =>
    if g = ops.zero then some (ops.normalize f)
    else loop ops n g (ops.remainder f g)

theorem loop_total [DecidableEq α] (ops : Operations α)
    (laws : Laws ops divides normalized) (n : Nat) :
    ∀ f g, ops.rank g < n →
      ∃ d, loop ops n f g = some d ∧ IsGCD divides f g d ∧ normalized d := by
  induction n with
  | zero =>
    intro f g h
    omega
  | succ n ih =>
    intro f g h
    by_cases hg : g = ops.zero
    · subst g
      refine ⟨ops.normalize f, ?_, ?_, laws.normalized_normalize f⟩
      · simp [loop]
      · refine ⟨?_, laws.divides_zero _, ?_⟩
        · exact (laws.normalize_divides f f).mpr (laws.divides_self f)
        · intro c hf _
          exact (laws.divides_normalize c f).mpr hf
    · have hr := laws.remainder_rank f g hg
      obtain ⟨d, hd, ⟨hdf, hdg, hgreat⟩, hn⟩ :=
        ih g (ops.remainder f g) (by omega)
      refine ⟨d, ?_, ?_, hn⟩
      · simp [loop, hg, hd]
      · have common := (laws.remainder_common f g d hg).mp ⟨hdf, hdg⟩
        refine ⟨common.1, common.2, ?_⟩
        intro c hf hg'
        have reduced := (laws.remainder_common f g c hg).mpr ⟨hf, hg'⟩
        exact hgreat c reduced.1 reduced.2

/-- Includes the initial call and the zero-divisor base case. -/
def iterations (ops : Operations α) (f g : α) : Nat :=
  max (ops.rank f) (ops.rank g) + 1

theorem input_bound_total [DecidableEq α] (ops : Operations α)
    (laws : Laws ops divides normalized) (f g : α) :
    ∃ d, loop ops (iterations ops f g) f g = some d ∧
      IsGCD divides f g d ∧ normalized d := by
  apply loop_total ops laws
  simp only [iterations]
  omega

/-- With polynomial rank at most degree + 1, max degree + 2 calls suffice. -/
theorem degree_bound_total [DecidableEq α] (ops : Operations α)
    (laws : Laws ops divides normalized) (degree : α → Nat)
    (rank_le : ∀ p, ops.rank p ≤ degree p + 1) (f g : α) :
    ∃ d, loop ops (max (degree f) (degree g) + 2) f g = some d ∧
      IsGCD divides f g d ∧ normalized d := by
  apply loop_total ops laws
  have := rank_le g
  omega

end Macaulean.M2.GCD.TotalCorrectness
