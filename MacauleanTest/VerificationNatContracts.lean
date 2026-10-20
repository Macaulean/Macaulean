import Macaulean.Verification.NatContracts

/-! Contracts for worksheet M2 functions over ℕ: the verification conditions are
generated from the compiled code, never written by hand, and wrong or unsupported
programs are refused. -/
open M2

#guard_msgs in
gcdNat = (a,b) -> if b == 0 then a else gcdNat(b, a % b);

/-- info: o2 = 21 : ZZ -/
#guard_msgs in
gcdNat(1071,462)

#guard_msgs in
#m2_verify gcdNat (a b : Nat) returns r : r = Nat.gcd a b
  termination_by b := by
    split
    · simp_all
    · exact ⟨Nat.mod_lt _ (by omega), by rw [Nat.gcd_comm b, ← Nat.gcd_rec, Nat.gcd_comm]⟩

/-- info: 'gcdNat.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gcdNat.correct

#guard_msgs in
sumTo = n -> if n == 0 then 0 else n + sumTo(n-1);

#guard_msgs in
#m2_verify sumTo (n : Nat) returns r : 2 * r = n * (n + 1)
  termination_by n := by
    split
    · simp_all
    · refine ⟨by omega, by omega, fun r hr => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp at hr
      grind

#guard_msgs in
pow2 = n -> if n == 0 then 1 else 2 * pow2(n-1);

#guard_msgs in
#m2_verify pow2 (n : Nat) returns r : r = 2 ^ n
  termination_by n := by
    split
    · simp_all
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [Nat.pow_succ, Nat.mul_comm]

#guard_msgs in
max2 = (a,b) -> if a < b then b else a;

#guard_msgs in
#m2_verify max2 (a b : Nat) returns r : a ≤ r ∧ b ≤ r ∧ (r = a ∨ r = b)

#guard_msgs in
predNat = n -> n - 1;

#guard_msgs in
#m2_verify predNat (n : Nat) (h : 0 < n) returns r : r + 1 = n

-- Boolean conditions short-circuit exactly as the runtime does.
#guard_msgs in
clamp = n -> if n < 3 or not (n <= 10) then 0 else n;

#guard_msgs in
#m2_verify clamp (n : Nat) returns r : r = 0 ∨ (3 ≤ r ∧ r ≤ 10 ∧ r = n)

#guard_msgs in
countDown = (k,acc) -> if k == 0 or acc >= 100 and k > 1 then acc else countDown(k - 1, acc + k);

#guard_msgs in
#m2_verify countDown (k acc : Nat) returns r : acc ≤ r
  termination_by k

-- A wrong postcondition leaves an unprovable verification condition, and no
-- `correct` theorem is installed.
#guard_msgs in
wrongMax = (a,b) -> if a < b then b else a;

#guard_msgs (drop error) in
#m2_verify wrongMax (a b : Nat) returns r : r = a

/-- info: Unknown identifier `wrongMax.correct` -/
#guard_msgs in
#check_failure wrongMax.correct

-- Unsupported programs are refused before any proof is attempted.
#guard_msgs in
loopy = n -> if n == 0 then 0 else loopy(n-1);

/-- error: `loopy` is recursive: give a decreasing measure with `termination_by` -/
#guard_msgs in
#m2_verify loopy (n : Nat) returns r : r = 0

#guard_msgs in
withLocal = n -> (m := n + 1; m);

/-- error: local variables in `withLocal` are not supported yet -/
#guard_msgs in
#m2_verify withLocal (n : Nat) returns r : r = n + 1

#guard_msgs in
callsOther = n -> predNat(n);

/--
error: `callsOther` is outside the supported natural-number fragment: calls to `predNat` are not supported; only self-recursion is
-/
#guard_msgs in
#m2_verify callsOther (n : Nat) returns r : True

/-- error: `predNat` takes 1 argument(s), but 2 natural-number binder(s) were given -/
#guard_msgs in
#m2_verify predNat (a b : Nat) returns r : True
