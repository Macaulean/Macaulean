import Macaulean.Interpreter.DSL

/-! Write M2, then inspect, execute, and prove facts about its Lean exports.
Open this file in Lean; generated declarations link back to their M2 input. -/
namespace DefinitionDemo
open M2

answer = 42;
square = x -> x*x;
gcd2 = (a,b) -> if b == 0 then a else gcd2(b,a%b);

-- Find the latest revision and inspect its definition, lowered code, and equation.
#m2_definition "gcd2"
#print M2Generated.gcd2
#print M2Generated.gcd2.code
#check M2Generated.gcd2.definition

-- Data exports have native Lean types.
example : M2Generated.answer = (42 : Int) := rfl

-- Function exports preserve M2's dynamic calling convention and explicit fuel.
#eval (M2Generated.square 64 (.zz 5)).map Prod.fst
example : (M2Generated.gcd2 128 (.sequence [.zz 48,.zz 18])).map Prod.fst =
    .ok (.zz 6) := by decide

-- Polynomial exports use the project's dimension-indexed polynomial type.
R = QQ[x];
p = x^2-1;
#check M2Generated.p
#check M2Generated.p.value_eq

-- Reassignment creates a new declaration; earlier Lean proofs retain their meaning.
answer = 43;
example : M2Generated.answer = (42 : Int) := rfl
example : M2Generated.answer.v2 = (43 : Int) := rfl
#m2_definition "answer"

end DefinitionDemo
