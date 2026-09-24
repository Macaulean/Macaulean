import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value

/-!
# Evaluator

A big-step evaluator for `Term`.  Everything here is structurally recursive and
free of `partial`/well-founded recursion, so the kernel can evaluate it and
facts such as `evalProgram t = .ok v` can be proved by `decide`.

The semantics follow Macaulay2's `value` function (so a trailing `;` does not
turn the result into `null`).  Integer `//` and `%` are Euclidean division,
which is exactly `Int.ediv`/`Int.emod` (Lean's `/` and `%` on `Int`).
-/

namespace Macaulean.M2

/-- Variable bindings, newest first. -/
abbrev Env := List (String × Value)

namespace Value

/-- The value as a rational number, if it is a number. -/
def toRat? : Value → Option Rat
  | zz n => some n
  | qq q => some q
  | _ => none

end Value

open Value

/-- Raise a rational number to an integer power, failing on `0 ^ negative`. -/
def ratZPow (q : Rat) (n : Int) : Except Error Value :=
  if n < 0 ∧ q = 0 then .error .divByZero else .ok (qq (q ^ n))

/-- Apply a binary operator to two values. -/
def evalBinOp (op : BinOp) (a b : Value) : Except Error Value :=
  match op, a, b with
  -- ring operations
  | .add, zz m, zz n => .ok (zz (m + n))
  | .sub, zz m, zz n => .ok (zz (m - n))
  | .mul, zz m, zz n => .ok (zz (m * n))
  -- `//` and `%` on `ZZ`: Euclidean division, with `m // 0 = 0` and `m % 0 = m`
  | .quot, zz m, zz n => .ok (zz (m / n))
  | .rem, zz m, zz n => .ok (zz (m % n))
  -- `//` and `%` on `QQ` (as a field): exact division, remainder zero
  | .quot, qq p, zz n => .ok (qq (if n = 0 then 0 else p / n))
  | .quot, qq p, qq q => .ok (qq (if q = 0 then 0 else p / q))
  | .rem, qq p, zz n => .ok (qq (if n = 0 then p else 0))
  | .rem, qq p, qq q => .ok (qq (if q = 0 then p else 0))
  -- powers
  | .pow, zz m, zz n => if 0 ≤ n then .ok (zz (m ^ n.toNat)) else ratZPow m n
  | .pow, qq p, zz n => ratZPow p n
  -- Boolean equality
  | .eq, .bool x, .bool y => .ok (.bool (x == y))
  | .ne, .bool x, .bool y => .ok (.bool (x != y))
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

/-- Apply a prefix operator to a value. -/
def evalUnOp : UnOp → Value → Except Error Value
  | .neg, zz n => .ok (zz (-n))
  | .neg, qq q => .ok (qq (-q))
  | .pos, zz n => .ok (zz n)
  | .pos, qq q => .ok (qq q)
  | op, v => .error (.noMethod op.symbol [v.className])

/-- Bindings present at startup. -/
def prelude : Env := [("true", .bool true), ("false", .bool false)]

/-- Names that cannot be assigned to. -/
def protectedNames : List String := prelude.map (·.1)

/-- Evaluate a term in an environment, returning its value and the new environment. -/
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
  | .assign x e, env => do
    if x ∈ protectedNames then throw (.protectedSymbol x)
    let (v, env) ← evalTerm e env
    return (v, (x, v) :: env)
  | .seq s e, env => do
    let (_, env) ← evalTerm s env
    evalTerm e env
  | .empty, env => .ok (null, env)

/-- Evaluate a closed program. -/
def evalProgram (t : Term) : Except Error Value :=
  (·.1) <$> evalTerm t prelude

end Macaulean.M2
