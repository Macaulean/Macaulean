import Macaulean.Interpreter.DSL

/-! Tests use ordinary Lean references, kernel reduction, and compiled execution.
No native M2 executable or verification frontend is required. -/
namespace DefinitionWorksheet
open M2

n = 7;
q = 2/3;
flag = true;
items = {n,q,flag};
pair = (n, q);
empty = null;

example : M2Generated.n = (7 : Int) := rfl
example : M2Generated.q = (mkRat 2 3) := by decide
example : M2Generated.flag = true := rfl
example : M2Generated.items = [.zz 7,.qq (mkRat 2 3),.bool true] := by decide
example : M2Generated.pair.value = .sequence M2Generated.pair := M2Generated.pair.value_eq
example : M2Generated.empty = Macaulean.M2.Value.null := rfl
example : M2Generated.n.value = .zz M2Generated.n := M2Generated.n.value_eq

square = x -> x*x;
example : (M2Generated.square 32 (.zz 5)).map Prod.fst = .ok (.zz 25) := by decide
-- A genuine compiled reference, not just evaluation inside the command elaborator.
/-- info: Except.ok (Macaulean.M2.Value.zz 36) -/
#guard_msgs in
#eval (M2Generated.square 32 (.zz 6)).map Prod.fst

example : M2Generated.square = Macaulean.M2.DefinitionExposure.run
    M2Generated.square.value M2Generated.square.state := M2Generated.square.definition

n = 9;
example : M2Generated.n = (7 : Int) := rfl
example : M2Generated.n.v2 = (9 : Int) := rfl

-- Captured cells are snapshotted, even when the function handle does not change.
counter := 0;
bump = () -> (counter = counter + 1; counter);
example : (M2Generated.bump 64 (.sequence [])).map Prod.fst = .ok (.zz 1) := by decide
bump();
example : (M2Generated.bump.v2 64 (.sequence [])).map Prod.fst = .ok (.zz 2) := by decide
example : (M2Generated.bump 64 (.sequence [])).map Prod.fst = .ok (.zz 1) := by decide

-- Recursive functions retain their own binding in the snapshot.
gcd2 = (a,b) -> if b == 0 then a else gcd2(b,a%b);
example : (M2Generated.gcd2 128 (.sequence [.zz 48,.zz 18])).map Prod.fst = .ok (.zz 6) := by decide
example : (M2Generated.gcd2 0 (.sequence [.zz 48,.zz 18])).map Prod.fst =
    .error .fuelExhausted := by decide

-- A function returning another function must preserve the returned heap.
makeAdder = x -> y -> x+y;
def useAdder : Except Macaulean.M2.Error Macaulean.M2.Value := do
  let (fn,state) ← M2Generated.makeAdder 64 (.zz 10)
  let (result,_) ← Macaulean.M2.Runtime.finish (Macaulean.M2.Runtime.call 64 fn (.zz 3) state)
  return result
example : useAdder = .ok (.zz 13) := by decide

-- Compositions and bindings created by effects are exported too.
composed = square@@square;
example : (M2Generated.composed 64 (.zz 2)).map Prod.fst = .ok (.zz 16) := by decide
publish = () -> (created = 23);
publish();
example : M2Generated.created = (23 : Int) := rfl

-- Ring generators and polynomials export native, dimension-indexed Lean data.
R = QQ[x,y];
p = x^2+2*x*y+y^2;
example : M2Generated.R.names = ["x","y"] := rfl
example : M2Generated.p.terms.length = 3 := by decide
example : M2Generated.p.value = .algebra (.poly M2Generated.R
    (Macaulean.M2.Polynomials.encode M2Generated.p)) := M2Generated.p.value_eq
example : (M2Generated.square.v2 32 (.zz 4)).map Prod.fst = .ok (.zz 16) := by decide

-- A library alias is callable with its library code and the same ring identity.
remainder = normalForm;
set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
example : (M2Generated.remainder 512
    (.sequence [M2Generated.p.value,.list [M2Generated.x.value]])).map Prod.fst =
    .ok (.algebra (.poly M2Generated.R [(1,[0,2])])) := by decide +kernel

-- Failed commands never publish values or new snapshots.
/-- error: division by zero -/
#guard_msgs in
failed = 1/0;
run_cmd do
  unless (← Macaulean.M2.DefinitionExposure.latest "failed").isNone do
    throwError "failed input published a Lean export"
  unless (← Lean.getEnv).contains ``M2Generated.p.definition do
    throwError "missing generated theorem"

-- Name discovery is available without importing the verification frontend.
/-- info: M2Generated.p
Inspect with #print DefinitionWorksheet.M2Generated.p, #print DefinitionWorksheet.M2Generated.p.code, or #print DefinitionWorksheet.M2Generated.p.definition -/
#guard_msgs in
#m2_definition "p"

end DefinitionWorksheet

namespace ExposureRollback
open M2
-- A user declaration in the reserved export namespace must not be overwritten.
def M2Generated.collision.code : Nat := 0
/-- error: M2 generated declaration already exists: ExposureRollback.M2Generated.collision.code -/
#guard_msgs in
collision = 123;
run_cmd do
  let env ← Lean.getEnv
  if env.contains `ExposureRollback.M2Generated.collision.value then
    throwError "partial export survived a declaration collision"
  if (← Macaulean.M2.DSL.getSession).lookup "collision" |>.isSome then
    throwError "failed export committed its worksheet binding"
  if (← Macaulean.M2.DefinitionExposure.latest "collision").isSome then
    throwError "failed export changed the latest registry"
end ExposureRollback

-- Generated proofs use kernel reflection, not sorry or native_decide.
/-- info: 'DefinitionWorksheet.M2Generated.square.definition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DefinitionWorksheet.M2Generated.square.definition
/-- info: 'DefinitionWorksheet.M2Generated.p.value_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DefinitionWorksheet.M2Generated.p.value_eq

-- Resetting execution does not reset the declaration supply or erase old exports.
run_cmd Macaulean.M2.DSL.resetSession
namespace DefinitionWorksheet
open M2
n = 11;
example : M2Generated.n = (7 : Int) := rfl
example : M2Generated.n.v3 = (11 : Int) := rfl
end DefinitionWorksheet
