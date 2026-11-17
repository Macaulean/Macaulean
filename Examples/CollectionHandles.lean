import Macaulean.Verification.Handles

/-! Immutable collections as Lean values in handle proofs. -/
open M2 Macaulean.M2

-- A single parameter receives the whole collection.
lengthOf = s -> #s;

example (xs : List Nat) : lengthOf xs ⇓ xs.length := by m2_unfold
example (s : Macaulean.M2.Seq Nat) : lengthOf s ⇓ s.values.length := by m2_unfold

-- The same M2 function works on lists and sequences.
join = (a,b) -> a | b;

theorem join_spec (xs ys : Macaulean.M2.Seq Nat) :
    join (xs, ys) ⇓ Macaulean.M2.Seq.mk (xs.values ++ ys.values) := by
  m2_unfold

-- Reuse a theorem returning a sequence, then verify its consumer.
joinedLength = (a,b) -> lengthOf(join(a,b));

example (xs ys : Macaulean.M2.Seq Nat) :
    joinedLength (xs, ys) ⇓ xs.values.length + ys.values.length := by
  m2_unfold
  m2_use join_spec xs ys
  m2_unfold

last = s -> s#-1;

example (xs : List Nat) (h : 0 < xs.length) : last xs ⇓ xs[xs.length - 1] := by
  m2_unfold
  congr 2 <;> omega
