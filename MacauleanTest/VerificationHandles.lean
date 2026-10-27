import Macaulean.Verification.Handles

/-! Worksheet functions as Lean terms: ordinary theorems about `f a ⇓ r` and `f a ↓`,
proved by induction with `m2_unfold`; modular reuse with `m2_use`; automatic
constants and live references. -/
open M2 Macaulean.M2

#guard_msgs in
gcdNat = (a,b) -> if b == 0 then a else gcdNat(b, a % b);

theorem gcdNat_spec (b a : Nat) : gcdNat (a, b) ⇓ Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    m2_unfold
    split
    · simp_all
    · rw [show Nat.gcd a b = Nat.gcd b (a % b) by
        rw [Nat.gcd_comm b, ← Nat.gcd_rec, Nat.gcd_comm]]
      exact ih _ (Nat.mod_lt _ (by omega)) _

theorem gcdNat_terminates (b a : Nat) : gcdNat (a, b) ↓ := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    m2_unfold
    intro hb
    exact ih _ (Nat.mod_lt _ (by omega)) _

-- The goal after one unfolding, as the user sees it.
/--
error: unsolved goals
a b : Nat
⊢ if b = 0 then a = a.gcd b else gcdNat (b, a % b) ⇓ a.gcd b
-/
#guard_msgs in
example (a b : Nat) : gcdNat (a, b) ⇓ Nat.gcd a b := by
  m2_unfold

-- Back to the raw runtime: termination, and every successful run returns gcd.
example (a b : Nat) : ∃ fuel v after,
    Runtime.call fuel M2.gcdNat.value (Arg.of (a, b)).value M2.gcdNat.state = .ok (v, after) :=
  (gcdNat_terminates b a).call

example (a b fuel : Nat) (v : Value) (after : Runtime.State)
    (h : Runtime.call fuel M2.gcdNat.value (Arg.of (a, b)).value M2.gcdNat.state = .ok (v, after)) :
    v = ToM2.toValue (Nat.gcd a b) :=
  (gcdNat_spec b a).sound h

example : gcdNat (12, 18) ⇓ 6 := by m2_eval

-- A live reference to the same function and worksheet state is the same constant.
example : (m2_fn% gcdNat) = M2.gcdNat := rfl
theorem gcd_live (b a : Nat) : (m2_fn% gcdNat) (a, b) ⇓ Nat.gcd a b := gcdNat_spec b a

-- Modularity: a later function uses `gcdNat_spec`, proved in an earlier state.
#guard_msgs in
twice = (a,b) -> gcdNat(a, b) + gcdNat(b, a);

theorem twice_spec (a b : Nat) : twice (a, b) ⇓ 2 * Nat.gcd a b := by
  m2_unfold
  m2_use gcdNat_spec b a
  m2_use gcdNat_spec a b
  rw [Nat.gcd_comm b a]; omega

-- A function equal to a Lean definition, by structural induction.
def triangle : Nat → Nat
  | 0 => 0
  | n+1 => (n+1) + triangle n

#guard_msgs in
sumTo = n -> if n == 0 then 0 else n + sumTo(n-1);

theorem sumTo_spec (n : Nat) : sumTo n ⇓ triangle n := by
  induction n with
  | zero => m2_unfold
  | succ n ih =>
    m2_unfold
    m2_use ih

-- Natural subtraction stays natural under the branch condition.
/--
error: unsolved goals
n : Nat
⊢ if n = 0 then 0 = triangle n
  else (sumTo (n - 1)).Sat fun vb => evalBinOp BinOp.add (Value.zz ↑n) vb = Except.ok (Value.zz ↑(triangle n))
-/
#guard_msgs in
example (n : Nat) : sumTo n ⇓ triangle n := by
  m2_unfold

-- Integers.
#guard_msgs in
absZ = x -> if x < 0 then -x else x;

theorem absZ_spec (x : Int) : absZ x ⇓ (x.natAbs : Int) := by
  m2_unfold; split <;> omega

-- Lists.
#guard_msgs in
len = l -> #l;

theorem len_spec (l : List Nat) : len l ⇓ l.length := by m2_unfold

#guard_msgs in
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

example : sumList ([3, 4, 5], 0) ⇓ 12 := by m2_eval

-- Forward references, redefinitions and live references.
/--
info: `M2.quad` captures the worksheet before [double] is defined; after defining it, use `m2_fn% quad`
-/
#guard_msgs in
quad = n -> double(double(n));

#guard_msgs in
double = n -> n + n;

theorem double_spec (n : Nat) : (m2_fn% double) n ⇓ 2 * n := by
  m2_unfold; omega

theorem quad_spec (n : Nat) : (m2_fn% quad) n ⇓ 4 * n := by
  m2_unfold
  m2_use double_spec n
  have := double_spec (2 * n)
  rw [show 2 * (2 * n) = 4 * n by omega] at this
  exact this

/-- info: the Lean constant for this definition of `double` is `M2.double_10` -/
#guard_msgs in
double = n -> 2 * n;

theorem double_spec' (n : Nat) : (m2_fn% double) n ⇓ 2 * n := by m2_unfold
example : (m2_fn% double) = M2.double_10 := rfl

-- After the redefinition, `quad` calls the new `double`, so the old spec no longer
-- applies, and the later state does not extend the earlier one.
theorem quad_spec' (n : Nat) : (m2_fn% quad) n ⇓ 4 * n := by
  m2_unfold
  m2_use double_spec' n
  have := double_spec' (2 * n)
  rw [show 2 * (2 * n) = 4 * n by omega] at this
  exact this

/--
error: m2_extends: the later worksheet state does not extend the earlier one (was a name redefined?)
⊢ Extends double.state double_10.state
-/
#guard_msgs in
example : Extends M2.double.state M2.double_10.state := by m2_extends

/-- info: 'twice_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twice_spec

/-- info: 'sumList_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sumList_spec
