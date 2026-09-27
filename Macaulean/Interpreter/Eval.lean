import Macaulean.Interpreter.Syntax
import Macaulean.Interpreter.Value
import Macaulean.Interpreter.PolynomialOps

/-! # Shared value operations and loop-free reference semantics -/
namespace Macaulean.M2
abbrev Env := List (String × Value)
namespace Value
def toRat? : Value → Option Rat
  | zz n => some n | qq q => some q | _ => none
mutual
def equalValue : Value → Value → Except Error Bool
  | .list xs, .list ys | .sequence xs, .sequence ys =>
    if xs.length = ys.length then equalElements xs ys else .ok false
  | .bool a, .bool b => .ok (a == b)
  | .null, .null => .ok true
  | .symbol a i, .symbol b j => .ok (a == b && i == j)
  | .algebra a, b => Polynomials.equal (.algebra a) b
  | a, .algebra b => Polynomials.equal a (.algebra b)
  | a, b => match a.toRat?, b.toRat? with
    | some p, some q => .ok (decide (p = q))
    | _, _ => .error (.noMethod "==" [a.className, b.className])
def equalElements : List Value → List Value → Except Error Bool
  | [], [] => .ok true
  | a :: xs, b :: ys => do
    if ← equalValue a b then equalElements xs ys else return false
  | _, _ => .ok false
end
end Value
open Value

def ratZPow (q : Rat) (n : Int) : Except Error Value :=
  if n < 0 ∧ q = 0 then .error .divByZero else .ok (qq (q ^ n))
def normalizedIndex (length : Nat) (index : Int) : Option Nat :=
  let j := if index < 0 then index + (length : Int) else index
  if 0 ≤ j ∧ j < (length : Int) then some j.toNat else none

def indexValue (xs : List Value) (index : Int) : Except Error Value := do
  let some j := normalizedIndex xs.length index | .error (.indexOutOfBounds index xs.length)
  let some v := xs[j]? | .error (.indexOutOfBounds index xs.length)
  return v

def rangeValues (first : Int) (count : Nat) : List Value :=
  (List.range count).map (fun (k : Nat) => .zz (first + Int.ofNat k))

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
  | .range, zz m, zz n => .ok (.sequence (rangeValues m (n - m + 1).toNat))
  | .rangeExclusive, zz m, zz n => .ok (.sequence (rangeValues m (n - m).toNat))
  | .repeat, zz n, v => .ok (.sequence (List.replicate n.toNat v))
  | .index, .list xs, zz i | .index, .sequence xs, zz i => indexValue xs i
  | .hasIndex, .list xs, zz i | .hasIndex, .sequence xs, zz i =>
    .ok (.bool (normalizedIndex xs.length i).isSome)
  | .hasIndex, .list xs, _ | .hasIndex, .sequence xs, _ => .ok (.bool false)
  | .hasIndex, .null, _ => .ok (.bool false)
  | .concat, .list xs, .list ys => .ok (.list (xs ++ ys))
  | .concat, .sequence xs, .sequence ys => .ok (.sequence (xs ++ ys))
  | .eq, .list xs, .list ys => .bool <$> Value.equalValue (.list xs) (.list ys)
  | .eq, .sequence xs, .sequence ys => .bool <$> Value.equalValue (.sequence xs) (.sequence ys)
  | .ne, .list xs, .list ys => (fun b => .bool (!b)) <$> Value.equalValue (.list xs) (.list ys)
  | .ne, .sequence xs, .sequence ys => (fun b => .bool (!b)) <$> Value.equalValue (.sequence xs) (.sequence ys)
  | .eq, .symbol x i, .symbol y j => .ok (.bool (x == y && i == j))
  | .ne, .symbol x i, .symbol y j => .ok (.bool (!(x == y && i == j)))
  | .eq, .bool x, .bool y => .ok (.bool (x == y))
  | .ne, .bool x, .bool y => .ok (.bool (x != y))
  | .eq, .null, .null => .ok (.bool true)
  | .ne, .null, .null => .ok (.bool false)
  | op, .algebra a, b => Polynomials.evalBinary op (.algebra a) b
  | op, a, .algebra b => Polynomials.evalBinary op a (.algebra b)
  | _, _, _ => match op, a.toRat?, b.toRat? with
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
  | .neg, zz n => .ok (zz (-n)) | .neg, qq q => .ok (qq (-q))
  | .pos, zz n => .ok (zz n) | .pos, qq q => .ok (qq q)
  | .notOp, .bool b => .ok (.bool (!b))
  | .length, .list xs | .length, .sequence xs => .ok (.zz xs.length)
  | op, .algebra a => Polynomials.evalUnary op (.algebra a)
  | op, v => .error (.noMethod op.symbol [v.className])
def evalLogicOp (op : LogicOp) (a b : Value) : Except Error Value :=
  match a, b with
  | .bool x, .bool y => .ok (.bool (match op with | .andOp => x && y | .orOp => x || y))
  | _, _ => .error (.noMethod op.symbol [a.className, b.className])
def prelude : Env :=
  [("true", .bool true), ("false", .bool false), ("null", .null)] ++ Polynomials.builtinEnv
def protectedNames : List String := prelude.map (·.1)

mutual
def evalTerm : Term → Env → Except Error (Value × Env)
  | .int n, env => .ok (zz n, env)
  | .var x, env => match env.lookup x with
    | some v => .ok (v, env) | none => .error (.unboundVar x)
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
    | .bool true => evalTerm yes env | .bool false => return (.null, env)
    | _ => throw (.conditionNotBoolean v.className)
  | .ifElse c yes no, env => do
    let (v, env) ← evalTerm c env
    match v with
    | .bool true => evalTerm yes env | .bool false => evalTerm no env
    | _ => throw (.conditionNotBoolean v.className)
  | .assign x e, env => do
    if x ∈ protectedNames then throw (.protectedSymbol x)
    let (v, env) ← evalTerm e env
    return (v, (x, v) :: env)
  | .indexAssign a i v, env => do
    let (a, env) ← evalTerm a env
    let (i, env) ← evalTerm i env
    let (v, _) ← evalTerm v env
    match a with
    | .list _ | .sequence _ => throw (.immutableCollection a.className)
    | _ => throw (.noMethod "#=" [a.className, i.className, v.className])
  | .seq s e, env => do
    let (_, env) ← evalTerm s env
    evalTerm e env
  | .empty, env => .ok (null, env)
  | .listLit elements, env => do
    let (values, env) ← evalTerms elements env
    return (.list values, env)
  | .sequence elements, env => do
    let (values, env) ← evalTerms elements env
    return (.sequence values, env)
  | .lambda .., _ | .apply .., _ | .localAssign .., _ | .assignMany .., _
  | .localSymbol .., _ | .returnTerm .., _ | .polyRing .., _ => .error .needsRuntime

def evalTerms : List Term → Env → Except Error (List Value × Env)
  | [], env => .ok ([], env)
  | t :: ts, env => do
    let (v, env) ← evalTerm t env
    let (vs, env) ← evalTerms ts env
    return (v :: vs, env)
end

def evalProgram (t : Term) : Except Error Value := (·.1) <$> evalTerm t prelude
end Macaulean.M2
