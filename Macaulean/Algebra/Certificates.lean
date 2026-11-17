import Macaulean.Algebra.Polynomial

/-!
# Kernel-checkable polynomial representation certificates

Certificate generation is untrusted. The checker recomputes coefficient-row
identities with the shared polynomial arithmetic. Accepted rows prove membership
in the mathematical generated ideal; checking rows in both directions proves
equality of ideals. This module alone does not assert the Gröbner property.
-/
namespace Macaulean.Algebra.Certificates
open Lean.Grind
open Macaulean.M2.KernelPolynomial

variable {R : Type} [CommRing R] [DecidableEq R] {n : Nat}

abbrev Poly (R : Type) (n : Nat) := Macaulean.Polynomial R n

/-- Equality is checked after normalization, not by evaluating at field points. -/
def equal (p q : Poly R n) : Bool := normalize p == normalize q

theorem equal_sound {p q : Poly R n} (h : equal p q = true) : Polynomial.Equivalent p q :=
  Polynomial.equivalent_of_normalize_eq p q (eq_of_beq h)

def linearCombination : List (Poly R n) → List (Poly R n) → Poly R n
  | a::as, g::gs => add (mul a g) (linearCombination as gs)
  | _, _ => Polynomial.zero

/-- A row has exactly one coefficient per generator. -/
def represents (p : Poly R n) (gs row : List (Poly R n)) : Bool :=
  row.length == gs.length && equal p (linearCombination row gs)

theorem generated_mono {gs hs : List (Poly R n)}
    (h : ∀ g ∈ gs, g ∈ hs) {p : Poly R n} (hp : Generated gs p) : Generated hs p := by
  induction hp with
  | zero => exact .zero
  | generator hg => exact .generator (h _ hg)
  | add _ _ ihp ihq => exact .add ihp ihq
  | mul a _ ih => exact .mul a ih
  | equivalent he _ ih => exact .equivalent he ih

theorem linearCombination_member (row gs : List (Poly R n)) :
    Generated gs (linearCombination row gs) := by
  induction row generalizing gs with
  | nil => exact .zero
  | cons a row ih =>
    cases gs with
    | nil => exact .zero
    | cons g gs =>
      exact .add (.mul a (.generator (by simp)))
        (generated_mono (by intro q hq; exact List.mem_cons_of_mem g hq) (ih gs))

theorem represents_dimension {p : Poly R n} {gs row : List (Poly R n)}
    (h : represents p gs row = true) : row.length = gs.length := by
  simp only [represents, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem represents_sound {p : Poly R n} {gs row : List (Poly R n)}
    (h : represents p gs row = true) : Generated gs p := by
  simp only [represents, Bool.and_eq_true] at h
  exact .equivalent (Polynomial.equivalent_symm (equal_sound h.2))
    (linearCombination_member row gs)

/-- Check one representation row for each target generator. Both dimensions are
validated, including empty presentations and zero generators. -/
def rows (targets generators : List (Poly R n)) : List (List (Poly R n)) → Bool
  | [] => targets.isEmpty
  | row::rest => match targets with
    | [] => false
    | p::ps => represents p generators row && rows ps generators rest

theorem rows_sound {targets generators : List (Poly R n)} {witnesses : List (List (Poly R n))}
    (h : rows targets generators witnesses = true) :
    ∀ p ∈ targets, Generated generators p := by
  induction witnesses generalizing targets with
  | nil =>
    cases targets with
    | nil => simp
    | cons p ps => simp [rows] at h
  | cons row rest ih =>
    cases targets with
    | nil => simp
    | cons p ps =>
      have hh : represents p generators row = true ∧ rows ps generators rest = true := by
        simpa only [rows, Bool.and_eq_true] using h
      intro q hq
      rcases List.mem_cons.mp hq with he | hm
      · subst q; exact represents_sound hh.1
      · exact ih hh.2 q hm

def sameIdeal (input basis : List (Poly R n))
    (basisInInput inputInBasis : List (List (Poly R n))) : Bool :=
  rows basis input basisInInput && rows input basis inputInBasis

theorem sameIdeal_sound {input basis : List (Poly R n)}
    {basisInInput inputInBasis : List (List (Poly R n))}
    (h : sameIdeal input basis basisInInput inputInBasis = true) :
    Ideal.Same (Ideal.span input) (Ideal.span basis) := by
  simp only [sameIdeal, Bool.and_eq_true] at h
  exact Ideal.span_same input basis (rows_sound h.2) (rows_sound h.1)

/-- Retain explicit rows with the proof, so a result remains inspectable and
usable without the process that found its coefficients. -/
structure Membership (p : Poly R n) (generators : List (Poly R n)) where
  coefficients : List (Poly R n)
  checked : represents p generators coefficients = true

theorem Membership.member {p : Poly R n} {generators : List (Poly R n)} (certificate : Membership p generators) : Generated generators p :=
  represents_sound certificate.checked

structure IdealEquality (input basis : List (Poly R n)) where
  basisInInput : List (List (Poly R n))
  inputInBasis : List (List (Poly R n))
  checked : sameIdeal input basis basisInInput inputInBasis = true

theorem IdealEquality.same {input basis : List (Poly R n)} (certificate : IdealEquality input basis) :
    Ideal.Same (Ideal.span input) (Ideal.span basis) := sameIdeal_sound certificate.checked

end Macaulean.Algebra.Certificates
