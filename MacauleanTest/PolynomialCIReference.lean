import MacauleanTest.PolynomialReference
import Macaulean.Interpreter.Check

/-! Minimal kernel regressions for the failing sorting path. These are not VM tests. -/
open Macaulean.M2
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
example : Polynomials.normalized 2 [(2,[0,1]),(1,[1,0]),(-2,[0,1]),(0,[9,9])] =
    .ok [(1,[1,0])] := by decide +kernel
example : Polynomials.mul 2 [(1,[1,0]),(1,[0,1])] [(1,[1,0]),(-1,[0,1])] =
    .ok [(1,[2,0]),(-1,[0,2])] := by decide +kernel
