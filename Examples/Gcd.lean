import Macaulean.Verification.NatContracts

/-!
# Verified M2 functions over natural numbers

Ordinary M2 defines a function; `#m2_verify` states its contract in Lean. Binders of
type `Nat` are the arguments, other binders are preconditions, the term after
`returns r :` is the postcondition, and `termination_by` gives a measure that every
self-call must decrease. Nothing about the M2 code is written in Lean by hand: the
verification conditions are computed from the function's compiled body.

For `gcdNat` below the generated condition is

    if b = 0 then a = Nat.gcd a b else a % b < b ∧ Nat.gcd b (a % b) = Nat.gcd a b

Replace the proof by `by trace_state; sorry` to see it in the InfoView. When the
`:= by ...` clause is omitted, simple conditions are closed automatically.
-/
open M2

gcdNat = (a,b) -> if b == 0 then a else gcdNat(b, a % b);

gcdNat(12,18)
gcdNat(1071,462)

#m2_verify gcdNat (a b : Nat) returns r : r = Nat.gcd a b
  termination_by b := by
    split
    · simp_all
    · exact ⟨Nat.mod_lt _ (by omega), by rw [Nat.gcd_comm b, ← Nat.gcd_rec, Nat.gcd_comm]⟩

/-! The generated theorem is about the runtime state of this worksheet. -/
#check @gcdNat.correct
#print axioms gcdNat.correct

/-! Subtraction stays in ℕ only with an obligation (`1 ≤ n` here). -/
sumTo = n -> if n == 0 then 0 else n + sumTo(n-1);

#m2_verify sumTo (n : Nat) returns r : 2 * r = n * (n + 1)
  termination_by n := by
    split
    · simp_all
    · refine ⟨by omega, by omega, fun r hr => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp at hr
      grind

/-! A precondition, discharged automatically. -/
predNat = n -> n - 1;

#m2_verify predNat (n : Nat) (h : 0 < n) returns r : r + 1 = n
