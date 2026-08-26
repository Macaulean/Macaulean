/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Macaulean.Grind.AlgPoly.Basic

@[expose] public section

/-!
# `ModVec`: residue-vector coefficients

A `CoeffRing` whose elements are vectors of residues, one modulo each entry of a
fixed list `ms : List Nat`.  Normalizing a polynomial with `ModVec ms`
coefficients is a *single-pass CRT*: instead of computing the exact integer
coefficients (which grow to thousands of bits and therefore into GMP), every
coefficient stays inside `[0, mᵢ)` for each `i`.

With all `mᵢ < 2^31` every intermediate product is `< 2^62`, i.e. inside Lean's
boxed-scalar range, so the kernel never calls a GMP routine while evaluating
these operations.  See `Macaulean/Grind/AlgPoly/KroneckerMod.lean` for the full
audit and for the theorem that turns "all residues vanish" into "the integer
coefficient vanishes".

The reduction map `ModVec.ofInt ms : Int → ModVec ms` is a `CoeffHom`
(`ofInt_isCoeffHom`), which is all the correspondence argument needs; `ModVec`
itself is *not* a ring (it is not even a `Zero`-preserving quotient unless the
`mᵢ` are positive) and `CoeffRing` deliberately demands no ring laws.
-/

namespace Macaulean

/-- A homomorphism between coefficient carriers.  Only the five operations that
`AlgExpr`/`KPoly` evaluation uses are constrained; no ring laws are needed. -/
structure CoeffHom {C : Type u} {C' : Type v} [CoeffRing C] [CoeffRing C']
    (ρ : C → C') : Prop where
  map_zero : ρ 0 = 0
  map_one : ρ 1 = 1
  map_add : ∀ a b, ρ (a + b) = ρ a + ρ b
  map_mul : ∀ a b, ρ (a * b) = ρ a * ρ b
  map_neg : ∀ a, ρ (-a) = -(ρ a)

/-- Coefficients as a vector of residues, one modulo each entry of `ms`. -/
structure ModVec (ms : List Nat) where
  vals : List Int

namespace ModVec

/-! ### Kernel-side vector operations

All of these walk `ms` and the value lists in lock-step, so the length of a
`ModVec` produced from `ofIntVals` is `ms.length` and stays there. -/

/-- Componentwise `(a + b) % mᵢ`. -/
def addVals : List Nat → List Int → List Int → List Int
  | m :: ms, a :: as, b :: bs => (a + b) % (m : Int) :: addVals ms as bs
  | _, _, _ => []

/-- Componentwise `(a * b) % mᵢ`. -/
def mulVals : List Nat → List Int → List Int → List Int
  | m :: ms, a :: as, b :: bs => (a * b) % (m : Int) :: mulVals ms as bs
  | _, _, _ => []

/-- Componentwise `(-a) % mᵢ`. -/
def negVals : List Nat → List Int → List Int
  | m :: ms, a :: as => (-a) % (m : Int) :: negVals ms as
  | _, _ => []

/-- The residue vector of a single integer. -/
def ofIntVals (k : Int) : List Nat → List Int
  | [] => []
  | m :: ms => k % (m : Int) :: ofIntVals k ms

/-- Structural equality of residue vectors. -/
def beqVals : List Int → List Int → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b && beqVals as bs
  | _, _ => false

theorem beqVals_sound : ∀ as bs : List Int, beqVals as bs = true → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [beqVals] at h
  | _ :: _, [], h => by simp [beqVals] at h
  | a :: as, b :: bs, h => by
    simp only [beqVals, Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [eq_of_beq h₁, beqVals_sound as bs h₂]

/-- Reduce an integer to its residue vector. -/
def ofInt (ms : List Nat) (k : Int) : ModVec ms := ⟨ofIntVals k ms⟩

instance instCoeffRing (ms : List Nat) : CoeffRing (ModVec ms) where
  zero := ⟨ofIntVals 0 ms⟩
  one := ⟨ofIntVals 1 ms⟩
  add a b := ⟨addVals ms a.vals b.vals⟩
  mul a b := ⟨mulVals ms a.vals b.vals⟩
  neg a := ⟨negVals ms a.vals⟩
  beq a b := beqVals a.vals b.vals
  beq_sound := by
    intro a b h
    cases a; cases b
    exact congrArg ModVec.mk (beqVals_sound _ _ h)

/-! ### `ofInt` is a `CoeffHom` -/

theorem ofIntVals_add (a b : Int) : ∀ ms : List Nat,
    ofIntVals (a + b) ms = addVals ms (ofIntVals a ms) (ofIntVals b ms)
  | [] => rfl
  | m :: ms => by
    show _ :: _ = _ :: _
    rw [ofIntVals_add a b ms, Int.add_emod]

theorem ofIntVals_mul (a b : Int) : ∀ ms : List Nat,
    ofIntVals (a * b) ms = mulVals ms (ofIntVals a ms) (ofIntVals b ms)
  | [] => rfl
  | m :: ms => by
    show _ :: _ = _ :: _
    rw [ofIntVals_mul a b ms, Int.mul_emod]

theorem neg_emod_emod (a n : Int) : (-a) % n = (-(a % n)) % n := by
  have h := Int.sub_emod 0 a n
  rw [Int.zero_sub, Int.zero_emod, Int.zero_sub] at h
  exact h

theorem ofIntVals_neg (a : Int) : ∀ ms : List Nat,
    ofIntVals (-a) ms = negVals ms (ofIntVals a ms)
  | [] => rfl
  | m :: ms => by
    show _ :: _ = _ :: _
    rw [ofIntVals_neg a ms, neg_emod_emod]

theorem ofInt_isCoeffHom (ms : List Nat) : CoeffHom (ofInt ms) where
  map_zero := rfl
  map_one := rfl
  map_add a b := congrArg ModVec.mk (ofIntVals_add a b ms)
  map_mul a b := congrArg ModVec.mk (ofIntVals_mul a b ms)
  map_neg a := congrArg ModVec.mk (ofIntVals_neg a ms)

/-! ### Vanishing residues are divisibility statements -/

theorem dvd_of_ofIntVals_eq_zero {k : Int} : ∀ ms : List Nat,
    ofIntVals k ms = ofIntVals 0 ms → ∀ m ∈ ms, (m : Int) ∣ k
  | [], _, _, hm => by cases hm
  | m :: ms, h, n, hn => by
    simp only [ofIntVals, List.cons.injEq] at h
    obtain ⟨h0, hrest⟩ := h
    have h0' : k % (m : Int) = 0 := by rw [h0, Int.zero_emod]
    cases hn with
    | head => exact Int.dvd_of_emod_eq_zero h0'
    | tail _ hn => exact dvd_of_ofIntVals_eq_zero ms hrest n hn

/-- If the residue vector of `k` is the zero vector, every modulus divides `k`. -/
theorem dvd_of_ofInt_eq_zero {ms : List Nat} {k : Int}
    (h : ofInt ms k = (0 : ModVec ms)) : ∀ m ∈ ms, (m : Int) ∣ k :=
  dvd_of_ofIntVals_eq_zero ms (congrArg ModVec.vals h)

end ModVec

end Macaulean

end
