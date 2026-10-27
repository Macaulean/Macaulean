import Macaulean.Verification.Handles.Intro
import Macaulean.Verification.Handles.Attr

/-!
# Production operations on represented values

These `m2_simp` lemmas evaluate the interpreter's own `evalBinOp`/`evalUnOp` on
integers (naturals are integers `.zz ↑n`) and Booleans, and discharge the side
conditions of `wpV`. They are all proved from the production definitions.
-/
namespace Macaulean.M2.Handles
open Lexical Macaulean.M2.Runtime

attribute [m2_simp] wpV wpArgs BinopPure UnopPure isBasis callable LogicOp.shortCircuit
  Verification.NatContracts.logicBool boolCase_bool Int.natCast_inj

section
variable (x y : Int)

@[m2_simp] theorem natV_zz (n : Nat) : Verification.NatContracts.natV n = .zz n := rfl
@[m2_simp] theorem toValue_nat (n : Nat) : ToM2.toValue n = Value.zz n := rfl
@[m2_simp] theorem toValue_int : ToM2.toValue x = Value.zz x := rfl
@[m2_simp] theorem toValue_bool (b : Bool) : ToM2.toValue b = Value.bool b := rfl
@[m2_simp] theorem toValue_value (v : Value) : ToM2.toValue v = v := rfl
@[m2_simp] theorem toValue_list {α : Type} [ToM2 α] (l : List α) :
    ToM2.toValue l = Value.list (l.map ToM2.toValue) := rfl

@[m2_simp] theorem zz_add : evalBinOp .add (.zz x) (.zz y) = .ok (.zz (x + y)) := rfl
@[m2_simp] theorem zz_sub : evalBinOp .sub (.zz x) (.zz y) = .ok (.zz (x - y)) := rfl
@[m2_simp] theorem zz_mul : evalBinOp .mul (.zz x) (.zz y) = .ok (.zz (x * y)) := rfl
@[m2_simp] theorem zz_quot : evalBinOp .quot (.zz x) (.zz y) = .ok (.zz (x / y)) := rfl
@[m2_simp] theorem zz_rem : evalBinOp .rem (.zz x) (.zz y) = .ok (.zz (x % y)) := rfl
@[m2_simp] theorem zz_pow (n : Nat) : evalBinOp .pow (.zz x) (.zz n) = .ok (.zz (x ^ n)) := by
  simp [evalBinOp]
@[m2_simp] theorem zz_eq : evalBinOp .eq (.zz x) (.zz y) = .ok (.bool (decide (x = y))) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_inj]
@[m2_simp] theorem zz_ne : evalBinOp .ne (.zz x) (.zz y) = .ok (.bool (decide (x ≠ y))) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_inj]
@[m2_simp] theorem zz_lt : evalBinOp .lt (.zz x) (.zz y) = .ok (.bool (decide (x < y))) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_lt_intCast]
@[m2_simp] theorem zz_le : evalBinOp .le (.zz x) (.zz y) = .ok (.bool (decide (x ≤ y))) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_le_intCast]
@[m2_simp] theorem zz_gt : evalBinOp .gt (.zz x) (.zz y) = .ok (.bool (decide (y < x))) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_lt_intCast]
@[m2_simp] theorem zz_ge : evalBinOp .ge (.zz x) (.zz y) = .ok (.bool (decide (y ≤ x))) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_le_intCast]
@[m2_simp] theorem zz_neg : evalUnOp .neg (.zz x) = .ok (.zz (-x)) := rfl
@[m2_simp] theorem bool_not (b : Bool) : evalUnOp .notOp (.bool b) = .ok (.bool !b) := rfl
@[m2_simp] theorem bool_eq (a b : Bool) :
    evalBinOp .eq (.bool a) (.bool b) = .ok (.bool (a == b)) := rfl
@[m2_simp] theorem list_length (xs : List Value) :
    evalUnOp .length (.list xs) = .ok (.zz xs.length) := rfl
end

/-! Lists: indexing by a natural number within bounds. -/
@[m2_simp] theorem list_index (xs : List Value) (i : Nat) (h : i < xs.length) :
    evalBinOp .index (.list xs) (.zz i) = .ok xs[i] := by
  have : ¬ (i : Int) < 0 := by omega
  simp [evalBinOp, indexValue, normalizedIndex, this, h, pure, Except.pure]

@[m2_simp] theorem list_index_map {α : Type} [ToM2 α] (l : List α) (i : Nat) (h : i < l.length) :
    evalBinOp .index (.list (l.map ToM2.toValue)) (.zz i) = .ok (ToM2.toValue l[i]) := by
  rw [list_index _ _ (by simpa using h)]
  simp

@[m2_simp] theorem list_index_ofNat (xs : List Value) (k : Nat) (h : OfNat.ofNat k < xs.length) :
    evalBinOp .index (.list xs) (.zz (no_index (OfNat.ofNat k))) = .ok xs[(OfNat.ofNat k : Nat)] :=
  list_index xs (OfNat.ofNat k) h

/-! Natural subtraction that stays natural, used with the branch conditions in scope. -/
theorem zz_sub_natCast {m n : Nat} (h : n ≤ m) :
    Value.zz ((m : Int) - (n : Int)) = Value.zz ((m - n : Nat) : Int) := by
  rw [Int.ofNat_sub h]
theorem zz_sub_ofNat (m k : Nat) (h : OfNat.ofNat k ≤ m) :
    Value.zz ((m : Int) - (no_index (OfNat.ofNat k : Int))) =
      Value.zz ((m - OfNat.ofNat k : Nat) : Int) := by
  rw [Int.ofNat_sub h]; rfl

end Macaulean.M2.Handles
