import Macaulean.Verification.Handles

/-!
# Worksheet M2 functions as Lean terms

Every M2 function definition below also defines a Lean constant: `gcdNat = ...`
gives `M2.gcdNat : Macaulean.M2.Fn`, written `gcdNat` under `open M2`. Theorems
about it are ordinary Lean theorems:

* `f a ⇓ r`: the call returns `r` (it terminates, and every run that finishes
  returns `r`);
* `f a ↓`: the call terminates.

Arguments and results are Lean values; a tuple `(a, b)` is an M2 sequence. In
proofs, `m2_unfold` replaces a call by one step of the function's body, written
with Lean operations; `m2_use h` uses a proved call; `m2_eval` evaluates concrete
calls. Termination is just the induction you choose.
-/
open M2 Macaulean.M2

gcdNat = (a,b) -> if b == 0 then a else gcdNat(b, a % b);

theorem gcdNat_spec (b a : Nat) : gcdNat (a, b) ⇓ Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    m2_unfold
    -- ⊢ if b = 0 then a = a.gcd b else gcdNat (b, a % b) ⇓ a.gcd b
    split
    · simp_all
    · rw [show Nat.gcd a b = Nat.gcd b (a % b) by
        rw [Nat.gcd_comm b, ← Nat.gcd_rec, Nat.gcd_comm]]
      exact ih _ (Nat.mod_lt _ (by omega)) _

/-! Termination on its own, and what it says about the raw runtime. -/
theorem gcdNat_terminates (b a : Nat) : gcdNat (a, b) ↓ := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    m2_unfold
    -- ⊢ ¬b = 0 → gcdNat (b, a % b) ↓
    intro hb
    exact ih _ (Nat.mod_lt _ (by omega)) _

example (a b : Nat) : ∃ fuel v after,
    Runtime.call fuel M2.gcdNat.value (Arg.of (a, b)).value M2.gcdNat.state = .ok (v, after) :=
  (gcdNat_terminates b a).call

example : gcdNat (12, 18) ⇓ 6 := by m2_eval

/-! A later function uses the earlier theorem. -/
twice = (a,b) -> gcdNat(a, b) + gcdNat(b, a);

theorem twice_spec (a b : Nat) : twice (a, b) ⇓ 2 * Nat.gcd a b := by
  m2_unfold
  m2_use gcdNat_spec b a
  m2_use gcdNat_spec a b
  -- ⊢ a.gcd b + b.gcd a = 2 * a.gcd b
  rw [Nat.gcd_comm b a]; omega

/-! Beyond ℕ: integers and lists. -/
absZ = x -> if x < 0 then -x else x;

theorem absZ_spec (x : Int) : absZ x ⇓ (x.natAbs : Int) := by
  m2_unfold; split <;> omega

sumList = (l,i) -> if i >= #l then 0 else l#i + sumList(l, i+1);

theorem sumList_spec (l : List Nat) (i : Nat) : sumList (l, i) ⇓ (l.drop i).sum := by
  induction h : l.length - i generalizing i with
  | zero =>
    m2_unfold
    rw [dif_pos (by omega), List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    m2_unfold
    rw [dif_neg (by omega)]
    m2_use ih (i + 1) (by omega)
    rw [List.drop_eq_getElem_cons (i := i) (l := l) (by omega), List.sum_cons]

/-! Live references: `m2_fn% name` is the function bound to `name` here, which
matters when a function calls one defined after it. -/
quad = n -> double(double(n));
double = n -> n + n;

theorem double_spec (n : Nat) : (m2_fn% double) n ⇓ 2 * n := by
  m2_unfold; omega

theorem quad_spec (n : Nat) : (m2_fn% quad) n ⇓ 4 * n := by
  m2_unfold
  m2_use double_spec n
  -- ⊢ double (2 * n) ⇓ 4 * n
  have := double_spec (2 * n)
  rw [show 2 * (2 * n) = 4 * n by omega] at this
  exact this
