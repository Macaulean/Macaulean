import Macaulean.Verification.Handles.Simp

/-!
# Immutable collections in handle proofs

These lemmas reduce the production operators on represented collections. Signed
indices count from the end; an invalid access remains a failed runtime operation.
-/
namespace Macaulean.M2.Handles

@[m2_simp] theorem toValue_seq {α : Type} [ToM2 α] (s : Seq α) :
    ToM2.toValue s = Value.sequence (s.values.map ToM2.toValue) := rfl

@[m2_simp] theorem sequence_length (xs : List Value) :
    evalUnOp .length (.sequence xs) = .ok (.zz xs.length) := rfl

@[m2_simp] theorem sequence_index (xs : List Value) (i : Nat) (h : i < xs.length) :
    evalBinOp .index (.sequence xs) (.zz i) = .ok xs[i] :=
  list_index xs i h

@[m2_simp] theorem sequence_index_map {α : Type} [ToM2 α]
    (xs : List α) (i : Nat) (h : i < xs.length) :
    evalBinOp .index (.sequence (xs.map ToM2.toValue)) (.zz i) =
      .ok (ToM2.toValue xs[i]) := list_index_map xs i h

@[m2_simp] theorem sequence_index_ofNat (xs : List Value) (k : Nat)
    (h : OfNat.ofNat k < xs.length) :
    evalBinOp .index (.sequence xs) (.zz (no_index (OfNat.ofNat k))) =
      .ok xs[(OfNat.ofNat k : Nat)] := sequence_index xs (OfNat.ofNat k) h

/-- Mathematical index after translating an index counted from the end. -/
def indexOffset (length : Nat) (i : Int) : Int :=
  if i < 0 then i + (length : Int) else i

private theorem indexValue_signed (xs : List Value) (i : Int) :
    indexValue xs i =
      if h : 0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length then
        .ok (getElem xs (indexOffset xs.length i).toNat (by unfold indexOffset at *; omega))
      else .error (.indexOutOfBounds i xs.length) := by
  by_cases h : 0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length
  · have hn : normalizedIndex xs.length i = some (indexOffset xs.length i).toNat := by
      change (if 0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length
        then some (indexOffset xs.length i).toNat else none) = _
      rw [if_pos h]
    have hb : (indexOffset xs.length i).toNat < xs.length := by omega
    simp [indexValue, hn, h, pure, Except.pure]
  · have hn : normalizedIndex xs.length i = none := by
      change (if 0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length
        then some (indexOffset xs.length i).toNat else none) = _
      rw [if_neg h]
    simp [indexValue, hn, h]

@[m2_simp] theorem list_concat (xs ys : List Value) :
    evalBinOp .concat (.list xs) (.list ys) = .ok (.list (xs ++ ys)) := rfl

@[m2_simp] theorem list_index_signed (xs : List Value) (i : Int)
    (h : 0 ≤ (if i < 0 then i + (xs.length : Int) else i) ∧
      (if i < 0 then i + (xs.length : Int) else i) < xs.length) :
    evalBinOp .index (.list xs) (.zz i) =
      .ok (getElem xs (indexOffset xs.length i).toNat (by unfold indexOffset at *; omega)) := by
  change indexValue xs i = _
  rw [indexValue_signed]
  simp only [indexOffset]
  split <;> rfl

@[m2_simp] theorem list_hasIndex (xs : List Value) (i : Int) :
    evalBinOp .hasIndex (.list xs) (.zz i) =
      .ok (.bool (decide (0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length))) := by
  change (Except.ok (.bool ((if 0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length
    then some (indexOffset xs.length i).toNat else none).isSome)) : Except Error Value) = _
  split <;> simp_all

@[m2_simp] theorem sequence_concat (xs ys : List Value) :
    evalBinOp .concat (.sequence xs) (.sequence ys) = .ok (.sequence (xs ++ ys)) := rfl

@[m2_simp] theorem sequence_index_signed (xs : List Value) (i : Int)
    (h : 0 ≤ (if i < 0 then i + (xs.length : Int) else i) ∧
      (if i < 0 then i + (xs.length : Int) else i) < xs.length) :
    evalBinOp .index (.sequence xs) (.zz i) =
      .ok (getElem xs (indexOffset xs.length i).toNat (by unfold indexOffset at *; omega)) := by
  change indexValue xs i = _
  rw [indexValue_signed]
  simp only [indexOffset]
  split <;> rfl

@[m2_simp] theorem sequence_hasIndex (xs : List Value) (i : Int) :
    evalBinOp .hasIndex (.sequence xs) (.zz i) =
      .ok (.bool (decide (0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length))) := by
  change (Except.ok (.bool ((if 0 ≤ indexOffset xs.length i ∧ indexOffset xs.length i < xs.length
    then some (indexOffset xs.length i).toNat else none).isSome)) : Except Error Value) = _
  split <;> simp_all

@[m2_simp] theorem list_index_signed_map {α : Type} [ToM2 α]
    (xs : List α) (i : Int)
    (h : 0 ≤ (if i < 0 then i + (xs.length : Int) else i) ∧
      (if i < 0 then i + (xs.length : Int) else i) < xs.length) :
    evalBinOp .index (.list (xs.map ToM2.toValue)) (.zz i) =
      .ok (ToM2.toValue (getElem xs (indexOffset xs.length i).toNat
        (by unfold indexOffset; omega))) := by
  simpa only [List.length_map, List.getElem_map] using
    list_index_signed (xs.map ToM2.toValue) i (by simpa using h)

@[m2_simp 1100] theorem list_hasIndex_nat (xs : List Value) (i : Nat) :
    evalBinOp .hasIndex (.list xs) (.zz i) = .ok (.bool (decide (i < xs.length))) := by
  rw [list_hasIndex]
  have h0 : ¬ (i : Int) < 0 := by omega
  have he : (0 ≤ (i : Int) ∧ (i : Int) < xs.length) ↔ i < xs.length := by omega
  simp only [indexOffset, if_neg h0, he]

@[m2_simp] theorem sequence_index_signed_map {α : Type} [ToM2 α]
    (xs : List α) (i : Int)
    (h : 0 ≤ (if i < 0 then i + (xs.length : Int) else i) ∧
      (if i < 0 then i + (xs.length : Int) else i) < xs.length) :
    evalBinOp .index (.sequence (xs.map ToM2.toValue)) (.zz i) =
      .ok (ToM2.toValue (getElem xs (indexOffset xs.length i).toNat
        (by unfold indexOffset; omega))) := by
  simpa only [List.length_map, List.getElem_map] using
    sequence_index_signed (xs.map ToM2.toValue) i (by simpa using h)

@[m2_simp 1100] theorem sequence_hasIndex_nat (xs : List Value) (i : Nat) :
    evalBinOp .hasIndex (.sequence xs) (.zz i) = .ok (.bool (decide (i < xs.length))) := by
  rw [sequence_hasIndex]
  have h0 : ¬ (i : Int) < 0 := by omega
  have he : (0 ≤ (i : Int) ∧ (i : Int) < xs.length) ↔ i < xs.length := by omega
  simp only [indexOffset, if_neg h0, he]

@[m2_simp] theorem sequence_range (a b : Int) :
    evalBinOp .range (.zz a) (.zz b) =
      .ok (ToM2.toValue (Seq.mk ((List.range (b - a + 1).toNat).map
        fun (k : Nat) => a + (k : Int)))) := by
  simp [evalBinOp, toValue_seq, rangeValues, List.map_map, toValue_int, Function.comp_def]

@[m2_simp] theorem sequence_rangeExclusive (a b : Int) :
    evalBinOp .rangeExclusive (.zz a) (.zz b) =
      .ok (ToM2.toValue (Seq.mk ((List.range (b - a).toNat).map
        fun (k : Nat) => a + (k : Int)))) := by
  simp [evalBinOp, toValue_seq, rangeValues, List.map_map, toValue_int, Function.comp_def]

@[m2_simp] theorem sequence_repeat (n : Int) (v : Value) :
    evalBinOp .repeat (.zz n) v = .ok (.sequence (List.replicate n.toNat v)) := rfl

-- Expose the bounds to the arithmetic discharger, including branch hypotheses.
attribute [m2_simp] indexOffset

end Macaulean.M2.Handles
