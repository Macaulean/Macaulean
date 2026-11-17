import Macaulean.Verification.RowProgram
import Macaulean.Verification.Fuel

/-!
# Weakest preconditions for M2 functions over natural numbers

A `Contract` is written by the user in Lean. `wpN`/`wpB` compute, from the compiled
`Code` of a function body, the proposition that the body returns a natural number
(resp. a Boolean) satisfying a postcondition, assuming every self-call meets the
contract on arguments of smaller measure. `Soundness.lean` proves once and for all
that these propositions are sufficient for the production runtime.

Every construct outside the supported fragment has weakest precondition `False`.
Subtraction yields an obligation `y ≤ x`, so all values stay natural numbers.
A self-call takes an explicit argument sequence or a single natural argument.
-/
namespace Macaulean.M2.Verification.NatContracts
open Lexical Macaulean.M2.Runtime

structure Contract where
  arity : Nat
  pre : List Nat → Prop
  post : List Nat → Nat → Prop
  measure : List Nat → Nat

/-- One body evaluation: the function's global name and parameter list, its contract,
the natural arguments in slots `0..k-1`, and the measure bound for recursive calls. -/
structure Ctx where
  name : String
  params : Parameters
  contract : Contract
  xs : List Nat
  bound : Nat

def natV (n : Nat) : Value := .zz n

/-- What a self-call on arguments `ys` must establish before using its result. -/
def Ctx.callPost (c : Ctx) (Q : Nat → Prop) (ys : List Nat) : Prop :=
  ys.length = c.contract.arity ∧ c.contract.pre ys ∧ c.contract.measure ys < c.bound ∧
    ∀ r, c.contract.post ys r → Q r

/-- Only a fixed parameter list unpacks an explicit argument sequence. -/
def Ctx.acceptsSequence (c : Ctx) : Prop :=
  match c.params with
  | .fixed _ => True
  | .variadic _ => False

def logicBool : LogicOp → Bool → Bool → Bool
  | .andOp, x, y => x && y
  | .orOp, x, y => x || y

mutual
def wpN (c : Ctx) : Code → (Nat → Prop) → Prop
  | .int z, Q => 0 ≤ z ∧ Q z.toNat
  | .read (.slot 0 i), Q => i < c.xs.length ∧ Q (c.xs.getD i 0)
  | .binop .add a b, Q => wpN c a fun x => wpN c b fun y => Q (x + y)
  | .binop .sub a b, Q => wpN c a fun x => wpN c b fun y => y ≤ x ∧ Q (x - y)
  | .binop .mul a b, Q => wpN c a fun x => wpN c b fun y => Q (x * y)
  | .binop .quot a b, Q => wpN c a fun x => wpN c b fun y => Q (x / y)
  | .binop .rem a b, Q => wpN c a fun x => wpN c b fun y => Q (x % y)
  | .binop .pow a b, Q => wpN c a fun x => wpN c b fun y => Q (x ^ y)
  | .ifElse cond yes no, Q => wpB c cond fun b => if b then wpN c yes Q else wpN c no Q
  | .apply (.read (.global f)) (.sequence args), Q => f = c.name ∧ c.acceptsSequence ∧ wpArgs c args (c.callPost Q)
  | .apply (.read (.global f)) arg, Q => f = c.name ∧ wpN c arg fun y => c.callPost Q [y]
  | _, _ => False

def wpB (c : Ctx) : Code → (Bool → Prop) → Prop
  | .binop .eq a b, Q => wpN c a fun x => wpN c b fun y => Q (decide (x = y))
  | .binop .ne a b, Q => wpN c a fun x => wpN c b fun y => Q (decide (x ≠ y))
  | .binop .lt a b, Q => wpN c a fun x => wpN c b fun y => Q (decide (x < y))
  | .binop .le a b, Q => wpN c a fun x => wpN c b fun y => Q (decide (x ≤ y))
  | .binop .gt a b, Q => wpN c a fun x => wpN c b fun y => Q (decide (y < x))
  | .binop .ge a b, Q => wpN c a fun x => wpN c b fun y => Q (decide (y ≤ x))
  | .logic op a b, Q => wpB c a fun x =>
      if x = op.shortCircuit then Q x else wpB c b fun y => Q (logicBool op x y)
  | .unop .notOp a, Q => wpB c a fun x => Q (!x)
  | _, _ => False

def wpArgs (c : Ctx) : List Code → (List Nat → Prop) → Prop
  | [], K => K []
  | a :: as, K => wpN c a fun y => wpArgs c as fun ys => K (y :: ys)
end

/-- The verification condition of a function body under its contract. -/
def VC (name : String) (params : Parameters) (C : Contract) (body : Code) : Prop :=
  ∀ xs, C.pre xs → wpN ⟨name, params, C, xs, C.measure xs⟩ body (C.post xs)

end Macaulean.M2.Verification.NatContracts
