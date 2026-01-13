import Macaulean.Factorization

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

example : ¬ Irreducible 60 := by
  m2reducible

/--
error: Tactic `m2reducible` failed: Cannot prove reducibility of 7

⊢ ¬Irreducible 7
-/
#guard_msgs in
example : ¬ Irreducible 7 :=
    by m2reducible

/--
error: Tactic `m2reducible` failed: Expected a goal of the form ¬ Irreducible x

⊢ Irreducible 7
-/
#guard_msgs in
example : Irreducible 7 :=
   by m2reducible
