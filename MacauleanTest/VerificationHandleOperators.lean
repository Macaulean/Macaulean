import Macaulean.Verification.Handles

/-! A single source operator dispatches by runtime representation. There is no
handle-specific arithmetic law per operand pair, including for a new wrapper. -/
open M2 Macaulean.M2

#guard_msgs in
addValues = (x,y) -> x+y;

theorem addValues_nat (x y : Nat) : addValues (x, y) ⇓ x+y := by m2_unfold
example (x y : Int) : addValues (x, y) ⇓ x+y := by m2_unfold
example (x y : Rat) : addValues (x, y) ⇓ x+y := by m2_unfold
example (x : Int) (y : Rat) : addValues (x, y) ⇓ (x : Rat)+y := by m2_unfold
example (x : Rat) (y : Int) : addValues (x, y) ⇓ x+(y : Rat) := by m2_unfold
example (x : Nat) (y : Rat) : addValues (x, y) ⇓ (x : Rat)+y := by m2_unfold
example (x : Rat) (y : Nat) : addValues (x, y) ⇓ x+(y : Rat) := by m2_unfold
example (x : Nat) (y : Int) : addValues (x, y) ⇓ (x : Int)+y := by m2_unfold
example (x : Int) (y : Nat) : addValues (x, y) ⇓ x+(y : Int) := by m2_unfold

structure WrappedInt where
  value : Int

instance : ToM2 WrappedInt := ⟨fun x => .zz x.value⟩

-- This is a representation rule, shared by every operator, not an addition law.
@[m2_simp] theorem toValue_wrappedInt (x : WrappedInt) :
    ToM2.toValue x = Value.zz x.value := rfl

example (x y : WrappedInt) : addValues (x, y) ⇓ WrappedInt.mk (x.value + y.value) := by
  m2_unfold
example (x : WrappedInt) (y : Rat) : addValues (x, y) ⇓ (x.value : Rat) + y := by
  m2_unfold

#guard_msgs in
arithmeticValues = (x,y) -> (x+y)*(x-y);
example (x y : WrappedInt) :
    arithmeticValues (x, y) ⇓ WrappedInt.mk ((x.value+y.value)*(x.value-y.value)) := by
  m2_unfold

-- Unresolved results stay behind handle calls until a theorem supplies a value.
#guard_msgs in
addTwice = (x,y) -> addValues(x,y) + addValues(y,x);
example (x y : Nat) : addTwice (x, y) ⇓ 2*(x+y) := by
  m2_unfold
  m2_use addValues_nat x y
  m2_use addValues_nat y x
  omega

-- Dispatch errors stay errors; overloading must not invent a Boolean addition.
example : evalBinOp .add (.bool true) (.bool false) =
    .error (.noMethod "+" ["Boolean", "Boolean"]) := by simp [m2_simp, BinOp.symbol, Value.className]

-- Keep symbolic arguments and unknown operators intact instead of splitting on
-- all possible runtime classes in the simplifier.
example (v w : Value) (r : Except Error Value) (h : evalBinOp .add v w = r) :
    evalBinOp .add v w = r := by
  try simp only [m2_simp]
  guard_target =ₛ evalBinOp .add v w = r
  exact h
example (op : BinOp) (x y : Int) (r : Except Error Value)
    (h : evalBinOp op (.zz x) (.zz y) = r) : evalBinOp op (.zz x) (.zz y) = r := by
  try simp only [m2_simp]
  guard_target =ₛ evalBinOp op (.zz x) (.zz y) = r
  exact h

-- Algebra values dispatch to the polynomial operator layer without unfolding its
-- implementation or assuming it agrees with an arbitrary Lean ring structure.
example (a b : Polynomials.Object) :
    evalBinOp .add (.algebra a) (.algebra b) =
      Polynomials.evalBinary .add (.algebra a) (.algebra b) := by
  simp only [m2_simp]

/-- info: 'addValues_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addValues_nat
