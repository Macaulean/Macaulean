import MacauleanTest.CollectionCases
import Macaulean.Interpreter.Wire

/-!
# Kernel checks for immutable collections

Every table entry is checked by Lean's kernel. Expected values are explicit data;
the tests never invoke a native evaluator to construct their proof certificates.
The extra depth is for the finite test table, not a change to interpreter semantics.
-/
namespace Macaulean.M2.CollectionsTest
open CollectionCases

set_option maxRecDepth 100000 in
example : successes.all (fun (source, value) => run source == .ok value) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
example : errors.all (fun (source, error) => run source == .error error) = true := by
  decide +kernel

private def parseFails (source : String) : Bool :=
  match run source with | .parseError _ => true | _ => false

set_option maxRecDepth 100000 in
example : invalidSyntax.all parseFails = true := by decide +kernel

-- These distinguish AST association from coincidentally equal outputs.
example : parse "1,2,3" = .ok (.sequence [.int 1, .int 2, .int 3]) := by decide +kernel
example : parse "((1,2),3)" = .ok (.sequence [.sequence [.int 1, .int 2], .int 3]) := by decide +kernel
example : parse "{(1,2)}" = .ok (.listLit [.sequence [.int 1, .int 2]]) := by decide +kernel
example : parse "{1..3}" = .ok (.listLit [.binop .range (.int 1) (.int 3)]) := by decide +kernel
example : parse "(1,,3)" = .ok (.sequence [.int 1, .empty, .int 3]) := by decide +kernel
example : parse "cp=1,2" = .ok (.sequence [.assign "cp" (.int 1), .int 2]) := by decide +kernel
example : parse "if true then 1 else 2,3" = .ok
    (.sequence [.ifElse (.var "true") (.int 1) (.int 2), .int 3]) := by decide +kernel
example : parse "1..3+4" = .ok (.binop .range (.int 1) (.binop .add (.int 3) (.int 4))) := by decide +kernel
example : parse "#cp#0" = .ok (.unop .length (.binop .index (.var "cp") (.int 0))) := by decide +kernel
example : parse "cp#0^2" = .ok (.binop .pow (.binop .index (.var "cp") (.int 0)) (.int 2)) := by decide +kernel
example : parse "cp|cq|cr" = .ok (.binop .concat (.binop .concat (.var "cp") (.var "cq")) (.var "cr")) := by decide +kernel
example : parse "1:2:3" = .ok (.binop .repeat (.int 1) (.binop .repeat (.int 2) (.int 3))) := by decide +kernel

-- Arbitrarily large integers remain integers; this tiny range must not truncate.
example : run "(10^40)..<(10^40+2)" = .ok
    (.sequence [.zz (10^40), .zz (10^40+1)]) := by decide +kernel
example : run "{1}#?(10^100)" = .ok (.bool false) := by decide +kernel
example : run "{1}#?(-10^100)" = .ok (.bool false) := by decide +kernel

-- The transport checks structure and leaf types, including integral rationals.
example : Value.ofWire ["List", "3", "ZZ", "1", "QQ", "1", "1", "Sequence", "0"] =
    .ok (.list [.zz 1, .qq (mkRat 1 1), .sequence []]) := by decide +kernel
example : Value.ofWire ["Sequence", "1", "Nothing"] = .ok (.sequence [.null]) := by decide +kernel

private def malformed : List (List String) := [
  [], ["List"], ["List", "-1"], ["List", "2", "ZZ", "1"],
  ["Sequence", "x"], ["Sequence", "999999999999999999999", "Nothing"],
  ["ZZ", "x"], ["QQ", "1", "0"], ["QQ", "1", "-3"],
  ["Boolean", "1"], ["Nothing", "garbage"], ["List", "0", "ZZ", "7"],
  ["unsupported", "MutableList"], ["Sequence", "1", "List", "1"]
]

example : malformed.all (fun w => !(Value.ofWire w).isOk) = true := by decide +kernel

set_option maxRecDepth 100000 in
example : successes.all (fun (_, v) => Value.ofWire v.toWire == .ok v) = true := by decide +kernel

-- Structural equality used by the checker must not erase scalar classes.
example : (Value.list [.zz 1] == Value.list [.qq (mkRat 1 1)]) = false := by decide +kernel
example : Value.equalValue (.list [.zz 1]) (.list [.qq (mkRat 1 1)]) = .ok true := by decide +kernel

end Macaulean.M2.CollectionsTest
