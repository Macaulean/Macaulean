import Macaulean.Interpreter.DSL

/-! Large literal exports must compile with Lean's default recursion limit. -/
namespace LargeExposure
open M2
big = 1..1025;
/-- info: 1025 -/
#guard_msgs in
#eval M2Generated.big.length
-- Preserve order across chunk boundaries and retain the final partial chunk.
example : M2Generated.big[31]? = some (.zz 32) := by decide
example : M2Generated.big[32]? = some (.zz 33) := by decide
/-- info: [Macaulean.M2.Value.zz 1024, Macaulean.M2.Value.zz 1025] -/
#guard_msgs in
#eval M2Generated.big.drop 1023
example : M2Generated.big.value = .sequence M2Generated.big := M2Generated.big.value_eq
headBig = () -> big#0;
/-- info: Except.ok (Macaulean.M2.Value.zz 1) -/
#guard_msgs in
#eval (M2Generated.headBig 32 (.sequence [])).map Prod.fst
end LargeExposure
