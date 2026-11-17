import Lean
import Init.GrindInstances.Ring.Rat

/-!
Generic algebraic obligations for the represented-polynomial reduction loop.
These lemmas prove a mathematical transition model, NOT its correspondence to
`Runtime.call`. The separate RuntimeReduction obligation records that missing
bridge. No abstract trace is advertised as verification of the DSL program.
-/
namespace Macaulean.M2.Verification.ProofJobs.Conservation
open Lean.Grind
variable {A : Type} [CommRing A]

/-- No truncating zip: malformed coefficient rows have no result. -/
def subtractRow (c : A) : List A → List A → Option (List A)
  | [], [] => some []
  | a::as, b::bs => (fun tail => (a-c*b)::tail) <$> subtractRow c as bs
  | _, _ => none

def dot : List A → List A → A
  | a::as, g::gs => a*g + dot as gs
  | _, _ => 0

theorem subtractRow_dimensions (c : A) (a b out : List A)
    (h : subtractRow c a b = some out) :
    a.length = b.length ∧ out.length = a.length := by
  induction a generalizing b out with
  | nil =>
    cases b <;> simp [subtractRow] at h
    cases h
    simp
  | cons x xs ih =>
    cases b with
    | nil => simp [subtractRow] at h
    | cons y ys =>
      cases hs : subtractRow c xs ys with
      | none => simp [subtractRow, hs] at h
      | some tail =>
        simp [subtractRow, hs] at h
        subst out
        obtain ⟨hab, hoa⟩ := ih ys tail hs
        simp [hab, hoa]

theorem subtractRow_wrong_length (c : A) (a b : List A)
    (h : a.length ≠ b.length) : subtractRow c a b = none := by
  cases hs : subtractRow c a b with
  | none => rfl
  | some out => exact False.elim (h (subtractRow_dimensions c a b out hs).1)

theorem dot_subtractRow (c : A) (a b out generators : List A)
    (h : subtractRow c a b = some out) :
    dot out generators = dot a generators - c * dot b generators := by
  induction a generalizing b out generators with
  | nil =>
    cases b <;> simp [subtractRow] at h
    cases h
    simp [dot] <;> grind
  | cons x xs ih =>
    cases b with
    | nil => simp [subtractRow] at h
    | cons y ys =>
      cases hs : subtractRow c xs ys with
      | none => simp [subtractRow, hs] at h
      | some tail =>
        simp [subtractRow, hs] at h
        subst out
        cases generators with
        | nil => simp [dot] <;> grind
        | cons g gs =>
          have ht := ih ys tail gs hs
          simp only [dot]
          grind

structure State (A : Type) where
  pending : A
  remainder : A
  coefficients : List A

def invariant (generators : List A) (s : State A) : Prop :=
  s.pending + s.remainder = dot s.coefficients generators

inductive Step (generators : List A) : State A → State A → Prop
  | move (s : State A) (term : A) :
      Step generators s ⟨s.pending-term, s.remainder+term, s.coefficients⟩
  | cancel (s : State A) (coefficient reducer : A) (row out : List A)
      (represented : reducer = dot row generators)
      (updated : subtractRow coefficient s.coefficients row = some out) :
      Step generators s ⟨s.pending-coefficient*reducer, s.remainder, out⟩

theorem step_preserves (generators : List A) (s next : State A)
    (hs : invariant generators s) (step : Step generators s next) :
    invariant generators next := by
  cases step with
  | move term =>
    simp only [invariant] at hs ⊢
    grind
  | cancel c g row out represented updated =>
    have hd := dot_subtractRow c s.coefficients row out generators updated
    simp only [invariant] at hs ⊢
    grind

inductive Trace (generators : List A) : State A → State A → Prop
  | refl (s : State A) : Trace generators s s
  | next {s mid last : State A} :
      Step generators s mid → Trace generators mid last → Trace generators s last

theorem trace_preserves (generators : List A) (s last : State A)
    (trace : Trace generators s last) (hs : invariant generators s) :
    invariant generators last := by
  revert hs
  induction trace with
  | refl => exact fun hs => hs
  | next step rest ih =>
    intro hs
    exact ih (step_preserves generators _ _ hs step)

theorem terminal_representation (generators : List A) (s last : State A)
    (trace : Trace generators s last) (hs : invariant generators s)
    (done : last.pending = 0) :
    last.remainder = dot last.coefficients generators := by
  have hl := trace_preserves generators s last trace hs
  simp only [invariant] at hl
  grind

end Macaulean.M2.Verification.ProofJobs.Conservation
