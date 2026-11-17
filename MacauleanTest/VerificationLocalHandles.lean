import Macaulean.Verification.Handles

/-! Universal handle proofs exercise local writes and both completion paths,
including early returns nested in operands. These use the production parser,
compiler and `m2_unfold`; concrete execution alone would not establish them. -/
open M2 Macaulean.M2

#guard_msgs in
localIncrement = n -> (x := n; x = x+1; x);

theorem localIncrement_spec (n : Nat) : localIncrement n ⇓ n+1 := by m2_unfold

#guard_msgs in
localAbs = n -> (x := n; if x < 0 then return -x; x);

theorem localAbs_spec (n : Int) : localAbs n ⇓ (if n < 0 then -n else n) := by
  m2_unfold
  split <;> omega

#guard_msgs in
returnSkipsWrite = n -> (return n; x := 1 / 0; x);

theorem returnSkipsWrite_spec (n : Nat) : returnSkipsWrite n ⇓ n := by m2_unfold

#guard_msgs in
returnInAssignment = n -> (x := (return n); 1 / 0);

theorem returnInAssignment_spec (n : Nat) : returnInAssignment n ⇓ n := by m2_unfold

#guard_msgs in
orderedWrites = n -> (x := n; (x = x+1) + (x = x+1));

theorem orderedWrites_spec (n : Nat) : orderedWrites n ⇓ 2*n+3 := by
  m2_unfold
  omega

#guard_msgs in
returnInRightOperand = n -> (x := n; (x = x+1) + (return x));

theorem returnInRightOperand_spec (n : Nat) : returnInRightOperand n ⇓ n+1 := by m2_unfold

#guard_msgs in
returnInLeftOperand = n -> (return n) + (1 / 0);

theorem returnInLeftOperand_spec (n : Nat) : returnInLeftOperand n ⇓ n := by m2_unfold

#guard_msgs in
returnInList = n -> {n+1, return n, 1 / 0};

theorem returnInList_spec (n : Nat) : returnInList n ⇓ n := by m2_unfold

#guard_msgs in
returnInSequence = n -> (n+1, return n, 1 / 0);

theorem returnInSequence_spec (n : Nat) : returnInSequence n ⇓ n := by m2_unfold

#guard_msgs in
returnInCondition = n -> if (return n) then 1 / 0 else 2;

theorem returnInCondition_spec (n : Nat) : returnInCondition n ⇓ n := by m2_unfold

#guard_msgs in
returnInCallArgument = n -> localIncrement(return n);

theorem returnInCallArgument_spec (n : Nat) : returnInCallArgument n ⇓ n := by m2_unfold

#guard_msgs in
returnInCallee = n -> (return n)(1 / 0);

theorem returnInCallee_spec (n : Nat) : returnInCallee n ⇓ n := by m2_unfold

#guard_msgs in
privateCaller = n -> (x := n; y := localIncrement(x); x = x+y; x);

theorem privateCaller_spec (n : Nat) : privateCaller n ⇓ 2*n+1 := by
  m2_unfold
  m2_use localIncrement_spec n
  omega

#guard_msgs in
privateRecursion = n -> (x := n; if x == 0 then return x; x = privateRecursion(x-1); x+1);

theorem privateRecursion_spec (n : Nat) : privateRecursion n ⇓ n := by
  induction n with
  | zero => m2_unfold
  | succ n ih =>
    m2_unfold
    simp only [not_false_eq_true, true_implies]
    m2_use ih

#guard_msgs in
uninitializedLocal = () -> (if false then x := 3; x);

theorem uninitializedLocal_spec : uninitializedLocal () ⇓ Value.null := by m2_unfold

#guard_msgs in
shortCircuitWrite = n -> (x := n; false and (x = x+1); x);

theorem shortCircuitWrite_spec (n : Nat) : shortCircuitWrite n ⇓ n := by m2_unfold

#guard_msgs in
logicReturn = n -> true and (return n);

theorem logicReturn_spec (n : Nat) : logicReturn n ⇓ n := by m2_unfold

#guard_msgs in
nestedReturnOperand = n -> return (return n);

theorem nestedReturnOperand_spec (n : Nat) : nestedReturnOperand n ⇓ n := by m2_unfold

#guard_msgs in
returnUnderNegation = n -> -(return n);

theorem returnUnderNegation_spec (n : Nat) : returnUnderNegation n ⇓ n := by m2_unfold

#guard_msgs in
returnInLeftLogic = n -> (return n) or (1 / 0);

theorem returnInLeftLogic_spec (n : Nat) : returnInLeftLogic n ⇓ n := by m2_unfold

#guard_msgs in
listWrites = n -> (x := n; {x = x+1, x = x+1, x});

theorem listWrites_spec (n : Nat) : listWrites n ⇓ [n+1, n+2, n+2] := by
  m2_unfold

#guard_msgs in
sequenceWrites = n -> (x := n; (x = x+1, x = x+1));

theorem sequenceWrites_spec (n : Nat) : sequenceWrites n ⇓
    Value.sequence [.zz (n+1), .zz (n+2)] := by
  m2_unfold

#guard_msgs in
parameterWrite = n -> (n = n+1; n);

theorem parameterWrite_spec (n : Nat) : parameterWrite n ⇓ n+1 := by m2_unfold

-- Reject effects outside the caller-preserving contract. The universal
-- soundness theorem must not prove these by treating their effects as pure.
open Macaulean.M2.Handles Macaulean.M2.Lexical in
theorem globalWrite_rejected (S : Runtime.State) (vs : List Value)
    (Q R : Value → List Value → Prop) :
    wpLocal S vs (.set (.global "x") (.int 1)) Q R = False := rfl

open Macaulean.M2.Handles Macaulean.M2.Lexical in
theorem capturedWrite_rejected (S : Runtime.State) (vs : List Value)
    (Q R : Value → List Value → Prop) :
    wpLocal S vs (.set (.slot 1 0) (.int 1)) Q R = False := rfl

open Macaulean.M2.Handles Macaulean.M2.Lexical in
theorem simultaneousWrite_rejected (S : Runtime.State) (vs : List Value)
    (Q R : Value → List Value → Prop) :
    wpLocal S vs (.setMany [.slot 0 0] (.int 1)) Q R = False := rfl

open Macaulean.M2.Handles Macaulean.M2.Lexical in
theorem invalidSlot_rejected (S : Runtime.State) :
    ¬ wpLocal S [] (.set (.slot 0 0) (.int 1)) (fun _ _ => True) (fun _ _ => True) := by
  simp [wpLocal]

/-- info: 'privateRecursion_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms privateRecursion_spec

/-- info: 'Macaulean.M2.Fn.Call.Sat.introLocalWp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Fn.Call.Sat.introLocalWp
