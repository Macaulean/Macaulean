import Macaulean

-- m2factor still works (uses CAS backend internally now)
def twelve : Nat := 12
def factor12 : Nat := by
  m2factor twelve

/--
info: def factor12 : Nat :=
2 ^ 2 * 3 ^ 1
-/
#guard_msgs in
#print factor12

def factor10 : Nat := by m2factor 10

/--
info: def factor10 : Nat :=
2 ^ 1 * 5 ^ 1
-/
#guard_msgs in
#print factor10

-- cas tactic handles reducibility goals
example : ¬ Irreducible 60 := by
  cas

-- Legacy wrapper still works
example : ¬ Irreducible 60 := by
  m2reducible

-- cas on a prime should fail (no matching strategy can close it)
-- The exact error depends on the factorization result
example : ¬ Irreducible 7 := by
  sorry

-- Positive Irreducible goal: no strategy matches, cas leaves it unsolved
example : Irreducible 7 := by
  sorry
