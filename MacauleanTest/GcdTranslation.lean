import Macaulean.Verification.Examples.GcdTranslation.Semantics

/-!
Concrete checks, not proofs of the universal preservation obligations.
Run with `lake env lean MacauleanTest/GcdTranslation.lean`.
No external M2 process, built-in gcd implementation, or theorem admission is used.
These checks were added by the PR; consult its validation section for execution status.
-/
namespace Macaulean.M2.Verification.Examples.GcdTranslation.Checks

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Only a concrete lowering identity, not `TODO.PlanPreserves`. -/
example : LoweringShape := ⟨rfl, rfl, rfl, rfl, rfl⟩

#guard parse "a = abs a; b = abs b" = .ok initializeTerm
#guard parse "b != 0" = .ok conditionTerm
#guard parse "r := a % b; a = b; b = r" = .ok iterationTerm
#guard parse "a" = .ok resultTerm
#guard parse "abs = (n) -> if n < 0 then -n else n" = .ok absDefinition

-- Baseline gap, NOT positive while coverage. Replace these two checks with a
-- while-node parse/lowering check when GCD-01 is implemented. The current lexer
-- accepts these spellings as identifiers; parse success alone is insufficient.
#guard Lexer.identifierToken "while" = .ident "while"
#guard Lexer.identifierToken "do" = .ident "do"

#guard iterationResult 32 1071 462 = .ok [.zz 462, .zz 147, .zz 147]
#guard iterationResult 32 462 147 = .ok [.zz 147, .zz 21, .zz 21]
#guard iterationResult 32 147 21 = .ok [.zz 21, .zz 0, .zz 0]

-- These execute the explicit CodePlan harness, not the whole source/DSL function.
#guard result 64 64 1071 462 = .ok (.zz 21)
#guard result 64 64 (-1071) 462 = .ok (.zz 21)
#guard result 64 64 1071 (-462) = .ok (.zz 21)
#guard result 64 64 (-1071) (-462) = .ok (.zz 21)
#guard result 64 64 0 0 = .ok (.zz 0)
#guard result 64 64 0 37 = .ok (.zz 37)
#guard result 64 64 37 0 = .ok (.zz 37)
#guard result 64 64 55 34 = .ok (.zz 1)
#guard result 0 64 1071 462 = .error .fuelExhausted
#guard result 64 0 1071 462 = .error .fuelExhausted

/-- Negative control: overwriting a before computing its remainder loses old a. -/
def wrongOrder : Lexical.Code :=
  .seq (.set aRef (.read bRef))
    (.seq (.set rRef (.binop .rem (.read aRef) (.read bRef)))
          (.set bRef (.read rRef)))

def wrongOrderResult : Except Error (List Value) := do
  let (cells, state) := ({} : Runtime.State).allocate [.zz 1071, .zz 462, .null]
  let (_, state) ← Runtime.finish (Runtime.eval 32 wrongOrder [cells] state)
  return [← Runtime.readRef aRef [cells] state,
          ← Runtime.readRef bRef [cells] state,
          ← Runtime.readRef rRef [cells] state]

#guard wrongOrderResult = .ok [.zz 462, .zz 0, .zz 0]
#guard wrongOrderResult ≠ iterationResult 32 1071 462

-- Existence of these declarations means the statements are available for proof,
-- not that their propositions have proofs. There is deliberately no TODO.Proofs value.
#check TODO.WritePreserves
#check TODO.LeafPreserves
#check TODO.PlanPreserves
#check TODO.PlanReflects
#check TODO.SourceTerminates
#check TODO.BodyTranslation
#print axioms remainder_leaf

end Macaulean.M2.Verification.Examples.GcdTranslation.Checks
