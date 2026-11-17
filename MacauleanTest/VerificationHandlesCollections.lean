import Macaulean.Verification.Handles

/-! Symbolic collection proofs, recursive calls, and runtime boundary behavior. -/
open M2 Macaulean.M2

#guard_msgs in
collectionLength = s -> #s;

example {α : Type} [ToM2 α] (xs : List α) : collectionLength xs ⇓ xs.length := by m2_unfold
example {α : Type} [ToM2 α] (s : Macaulean.M2.Seq α) : collectionLength s ⇓ s.values.length := by m2_unfold

#guard_msgs in
joinCollections = (a,b) -> a | b;

theorem joinLists_spec {α : Type} [ToM2 α] (xs ys : List α) :
    joinCollections (xs, ys) ⇓ xs ++ ys := by m2_unfold

theorem joinSequences_spec {α : Type} [ToM2 α] (xs ys : Macaulean.M2.Seq α) :
    joinCollections (xs, ys) ⇓ Macaulean.M2.Seq.mk (xs.values ++ ys.values) := by m2_unfold

#guard_msgs in
joinedLength = (a,b) -> collectionLength(joinCollections(a,b));

example {α : Type} [ToM2 α] (xs ys : Macaulean.M2.Seq α) :
    joinedLength (xs, ys) ⇓ xs.values.length + ys.values.length := by
  m2_unfold
  m2_use joinSequences_spec xs ys
  m2_unfold

#guard_msgs in
atCollection = (s,i) -> s#i;
#guard_msgs in
hasCollectionIndex = (s,i) -> s#?i;
#guard_msgs in
lastCollection = s -> s#-1;

example {α : Type} [ToM2 α] (s : Macaulean.M2.Seq α) (i : Nat) (h : i < s.values.length) :
    atCollection (s, i) ⇓ s.values[i] := by m2_unfold
example {α : Type} [ToM2 α] (xs : List α) (i : Nat) (h : i < xs.length) :
    atCollection (xs, i) ⇓ xs[i] := by m2_unfold

example {α : Type} [ToM2 α] (s : Macaulean.M2.Seq α) (h : 0 < s.values.length) :
    lastCollection s ⇓ s.values[s.values.length - 1] := by
  m2_unfold
  congr 2 <;> omega
example {α : Type} [ToM2 α] (xs : List α) (h : 0 < xs.length) :
    lastCollection xs ⇓ xs[xs.length - 1] := by
  m2_unfold
  congr 2 <;> omega

example (s : Macaulean.M2.Seq Nat) (i : Nat) : hasCollectionIndex (s, i) ⇓ decide (i < s.values.length) := by
  m2_unfold

#guard_msgs in
checkedIndex = (s,i) -> if s#?i then s#i else 0;

example (xs : List Nat) (i : Int) : checkedIndex (xs, i) ⇓
    (if h : 0 ≤ Handles.indexOffset xs.length i ∧ Handles.indexOffset xs.length i < xs.length
     then getElem xs (Handles.indexOffset xs.length i).toNat (by omega) else 0) := by
  m2_unfold
  split <;> simp_all

#guard_msgs in
sumSequence = (s,i) -> if i >= #s then 0 else s#i + sumSequence(s, i+1);

theorem sumSequence_spec (s : Macaulean.M2.Seq Nat) (i : Nat) :
    sumSequence (s, i) ⇓ (s.values.drop i).sum := by
  induction h : s.values.length - i generalizing i with
  | zero =>
    m2_unfold
    rw [dif_pos (by omega), List.drop_eq_nil_of_le (by omega)]; rfl
  | succ k ih =>
    m2_unfold
    rw [dif_neg (by omega)]
    m2_use ih (i + 1) (by omega)
    rw [List.drop_eq_getElem_cons (i := i) (l := s.values) (by omega), List.sum_cons]

#guard_msgs in
makeRange = (a,b) -> a..b;
#guard_msgs in
makeExclusiveRange = (a,b) -> a..<b;
#guard_msgs in
repeatValue = (n,x) -> n:x;

example (a b : Int) : makeRange (a, b) ⇓
    Macaulean.M2.Seq.mk ((List.range (b - a + 1).toNat).map fun (k : Nat) => a + (k : Int)) := by m2_unfold
example (a b : Int) : makeExclusiveRange (a, b) ⇓
    Macaulean.M2.Seq.mk ((List.range (b - a).toNat).map fun (k : Nat) => a + (k : Int)) := by m2_unfold
example {α : Type} [ToM2 α] (n : Int) (x : α) :
    repeatValue (n, x) ⇓ Macaulean.M2.Seq.mk (List.replicate n.toNat x) := by m2_unfold

#guard_msgs in
makeListPair = (x,y) -> {x,y};
#guard_msgs in
makeSequencePair = (x,y) -> (x,y);

example {α : Type} [ToM2 α] (x y : α) : makeListPair (x, y) ⇓ [x,y] := by m2_unfold
example {α : Type} [ToM2 α] (x y : α) :
    makeSequencePair (x, y) ⇓ Macaulean.M2.Seq.mk [x,y] := by m2_unfold
example : collectionLength (Macaulean.M2.Seq.mk [Macaulean.M2.Seq.mk [7,8]]) ⇓ 1 := by m2_eval

-- Unproved index bounds must not yield a proof of successful access.
example (xs : List Nat) (i : Nat) (h : i < xs.length) : atCollection (xs, i) ↓ := by
  fail_if_success solve | (clear h; m2_unfold)
  m2_unfold

-- A single parameter receives the whole sequence, including zero/one elements.
example : collectionLength (Macaulean.M2.Seq.mk ([] : List Nat)) ⇓ 0 := by m2_eval
example : collectionLength (Macaulean.M2.Seq.mk [7]) ⇓ 1 := by m2_eval
example : atCollection (Macaulean.M2.Seq.mk [7], (0 : Nat)) ⇓ 7 := by m2_eval
example : lastCollection (Macaulean.M2.Seq.mk [7]) ⇓ 7 := by m2_eval
example : hasCollectionIndex (Macaulean.M2.Seq.mk [7], (-2 : Int)) ⇓ false := by m2_eval
example : hasCollectionIndex (Macaulean.M2.Seq.mk [7], (1 : Nat)) ⇓ false := by m2_eval
example : sumSequence (Macaulean.M2.Seq.mk [3, 4, 5], (0 : Nat)) ⇓ 12 := by m2_eval
example : makeRange ((3 : Int), (1 : Int)) ⇓ Macaulean.M2.Seq.mk ([] : List Int) := by m2_eval
example : repeatValue ((-1 : Int), (7 : Nat)) ⇓ Macaulean.M2.Seq.mk ([] : List Nat) := by m2_eval

-- Fixed parameter lists still unpack sequences, exactly as tuple arguments do.
#guard_msgs in
addPair = (a,b) -> a+b;
example (a b : Nat) : addPair (a, b) ⇓ a + b := by m2_unfold
example (a b : Nat) : addPair (Macaulean.M2.Seq.mk [a, b]) ⇓ a + b := by m2_unfold
example : Runtime.arguments (.fixed ["a", "b"]) (ToM2.toValue (Macaulean.M2.Seq.mk [7])) =
    .error (.arity 2 1) := rfl

example : evalBinOp .index (.sequence []) (.zz 0) = .error (.indexOutOfBounds 0 0) := by decide
example : evalBinOp .index (.list [.zz 7]) (.zz 1) = .error (.indexOutOfBounds 1 1) := by decide
example : evalBinOp .index (.sequence [.zz 7]) (.zz (-2)) =
    .error (.indexOutOfBounds (-2) 1) := by decide
example : evalBinOp .concat (.list []) (.sequence []) =
    .error (.noMethod "|" ["List", "Sequence"]) := by decide

/-- info: 'sumSequence_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sumSequence_spec
