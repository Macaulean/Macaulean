import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value

/-!
# Structurally recursive scalar evaluation

All computation is pure and kernel-executable. Control-flow operands are
selected before evaluation. Blocks sequence in the same environment; they do
not create lexical scopes. As before, `Except` makes each input transactional.
-/

namespace Macaulean.M2

abbrev Env := List (String × Value)

namespace Value

def toRat? : Value → Option Rat
  | zz n => some n
  | qq q => some q
  | _ => none

end Value

open Value

def ratZPow (q : Rat) (n : Int) : Except Error Value :=
  if n < 0 ∧ q = 0 then .error .divByZero else .ok (qq (q ^ n))

def evalBinOp (op : BinOp) (a b : Value) : Except Error Value :=
  match op, a, b with
  | .add, zz m, zz n => .ok (zz (m + n))
  | .sub, zz m, zz n => .ok (zz (m - n))
  | .mul, zz m, zz n => .ok (zz (m * n))
  | .quot, zz m, zz n => .ok (zz (m / n))
  | .rem, zz m, zz n => .ok (zz (m % n))
  | .quot, qq p, zz n => .ok (qq (if n = 0 then 0 else p / n))
  | .quot, qq p, qq q => .ok (qq (if q = 0 then 0 else p / q))
  | .rem, qq p, zz n => .ok (qq (if n = 0 then p else 0))
  | .rem, qq p, qq q => .ok (qq (if q = 0 then p else 0))
  | .pow, zz m, zz n => if 0 ≤ n then .ok (zz (m ^ n.toNat)) else ratZPow m n
  | .pow, qq p, zz n => ratZPow p n
  | .eq, .bool x, .bool y => .ok (.bool (x == y))
  | .ne, .bool x, .bool y => .ok (.bool (x != y))
  | .eq, .null, .null => .ok (.bool true)
  | .ne, .null, .null => .ok (.bool false)
  | _, _, _ =>
    match op, a.toRat?, b.toRat? with
    | .add, some p, some q => .ok (qq (p + q))
    | .sub, some p, some q => .ok (qq (p - q))
    | .mul, some p, some q => .ok (qq (p * q))
    | .div, some p, some q => if q = 0 then .error .divByZero else .ok (qq (p / q))
    | .eq, some p, some q => .ok (.bool (decide (p = q)))
    | .ne, some p, some q => .ok (.bool (decide (p ≠ q)))
    | .lt, some p, some q => .ok (.bool (decide (p < q)))
    | .le, some p, some q => .ok (.bool (decide (p ≤ q)))
    | .gt, some p, some q => .ok (.bool (decide (q < p)))
    | .ge, some p, some q => .ok (.bool (decide (q ≤ p)))
    | _, _, _ => .error (.noMethod op.symbol [a.className, b.className])

def evalUnOp : UnOp → Value → Except Error Value
  | .neg, zz n => .ok (zz (-n))
  | .neg, qq q => .ok (qq (-q))
  | .pos, zz n => .ok (zz n)
  | .pos, qq q => .ok (qq q)
  | .notOp, .bool b => .ok (.bool (!b))
  | op, v => .error (.noMethod op.symbol [v.className])

/-- Dispatch after the non-short-circuited operands have been evaluated. -/
def evalLogicOp (op : LogicOp) (a b : Value) : Except Error Value :=
  match a, b with
  | .bool x, .bool y => .ok (.bool (match op with
      | .andOp => x && y
      | .orOp => x || y))
  | _, _ => .error (.noMethod op.symbol [a.className, b.className])

def prelude : Env := [("true", .bool true), ("false", .bool false), ("null", .null)]

def protectedNames : List String := prelude.map (·.1)

def evalTerm : Term → Env → Except Error (Value × Env)
  | .int n, env => .ok (zz n, env)
  | .var x, env =>
    match env.lookup x with
    | some v => .ok (v, env)
    | none => .error (.unboundVar x)
  | .unop op a, env => do
    let (v, env) ← evalTerm a env
    return (← evalUnOp op v, env)
  | .binop op a b, env => do
    let (va, env) ← evalTerm a env
    let (vb, env) ← evalTerm b env
    return (← evalBinOp op va vb, env)
  | .logic op a b, env => do
    let (va, env) ← evalTerm a env
    if va = .bool op.shortCircuit then return (va, env)
    let (vb, env) ← evalTerm b env
    return (← evalLogicOp op va vb, env)
  | .ifThen c yes, env => do
    let (v, env) ← evalTerm c env
    match v with
    | .bool true => evalTerm yes env
    | .bool false => return (.null, env)
    | _ => throw (.conditionNotBoolean v.className)
  | .ifElse c yes no, env => do
    let (v, env) ← evalTerm c env
    match v with
    | .bool true => evalTerm yes env
    | .bool false => evalTerm no env
    | _ => throw (.conditionNotBoolean v.className)
  | .assign x e, env => do
    if x ∈ protectedNames then throw (.protectedSymbol x)
    let (v, env) ← evalTerm e env
    return (v, (x, v) :: env)
  | .seq s e, env => do
    let (_, env) ← evalTerm s env
    evalTerm e env
  | .empty, env => .ok (null, env)

def evalProgram (t : Term) : Except Error Value :=
  (·.1) <$> evalTerm t prelude

end Macaulean.M2
