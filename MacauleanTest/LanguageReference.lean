import Macaulean.Interpreter.Run
import Macaulean.Interpreter.Session

/-! Named executable anchors for docs/m2-language-reference.md.
These test the implemented dialect; rejection is not a claim of native-M2 invalidity. -/
namespace Macaulean.M2.LanguageReference
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem power_left : run "2^3^2" = .ok (.zz 64) := by decide +kernel
theorem application_right : run "f=x->x+1; g=x->2*x; f g 3" = .ok (.zz 7) := by decide +kernel
theorem power_before_call : run "f=x->x+1; f(3)^2" = .ok (.zz 10) := by decide +kernel
theorem grouped_call : run "f=x->x+1; (f 3)^2" = .ok (.zz 16) := by decide +kernel
theorem negative_argument : run "f=x->x+1; f(-3)" = .ok (.zz (-2)) := by decide +kernel
theorem comparison_not : run "not 1 == 2 and true" = .ok (.bool true) := by decide +kernel
theorem assignment_comma : run "x=1,2; x" = .ok (.zz 1) := by decide +kernel
theorem grouped_sequence : run "x=(1,2); x" = .ok (.sequence [.zz 1,.zz 2]) := by decide +kernel
theorem no_splicing : run "{1..3}" = .ok (.list [.sequence [.zz 1,.zz 2,.zz 3]]) := by decide +kernel
theorem omitted_operand : run "(1,)" = .ok (.sequence [.zz 1,.null]) := by decide +kernel
theorem block_no_scope : run "x=1; (x:=2; x); x" = .ok (.zz 2) := by decide +kernel
theorem captured_cells : run "make=()->(n:=0; ()->(n=n+1)); f=make(); f(); f()" =
    .ok (.zz 2) := by decide +kernel
theorem source_order : run "x=7; f=()->(y:=x; x:=9; y); f()" = .ok (.zz 7) := by decide +kernel
theorem variadic_sequence : run "f=x->#x; f(1,2)" = .ok (.zz 2) := by decide +kernel
theorem fixed_arity : run "f=(x,y)->x+y; f({1,2})" = .error (.arity 2 1) := by decide +kernel
theorem early_return : run "x=0; f=()->(x=3; return 7; x=99); (f(),x)" =
    .ok (.sequence [.zz 7,.zz 3]) := by decide +kernel
theorem short_circuit : run "x=0; false and (x=1); x" = .ok (.zz 0) := by decide +kernel
theorem recursive_call : run "fact=n->if n==0 then 1 else n*fact(n-1); fact 5" =
    .ok (.zz 120) := by decide +kernel
theorem depth_failure : runWithFuel 20 "f=x->f x; f 0" = .error .fuelExhausted := by decide +kernel
theorem immutable_list : run "a={1,2}; a#0=3" = .error (.immutableCollection "List") := by decide +kernel
theorem strict_classes : run "1 === 1/1" = .ok (.bool false) := by decide +kernel
theorem numeric_promotion : run "1 == 1/1" = .ok (.bool true) := by decide +kernel
theorem rings_and_promotion : run "R=QQ[x,y]; (x+y)^2 == x^2+2*x*y+y^2" =
    .ok (.bool true) := by decide +kernel
theorem ordered_reduction : run "R=QQ[x,y]; normalForm(x^2+y,{x^2}) == y" =
    .ok (.bool true) := by decide +kernel
theorem provenance_matrix : run "R=QQ[x]; I=ideal(x^2-1,x-1); G=gb I; gens I * getChangeMatrix G == gens G" =
    .ok (.bool true) := by decide +kernel
theorem unassigned_global : run "unknownName" = .error (.unboundVar "unknownName") := by decide +kernel
-- Unsupported loop words are not reserved keywords in this dialect.
theorem loop_word_is_identifier : run "while=7; while" = .ok (.zz 7) := by decide +kernel

def rejectedSyntax (source : String) : Bool :=
  match parse source with | .error _ => true | .ok _ => false

theorem strings_outside : rejectedSyntax "\"hello\"" = true := by decide +kernel
theorem floats_outside : rejectedSyntax "1.5" = true := by decide +kernel
theorem subscripts_outside : rejectedSyntax "x_0" = true := by decide +kernel
theorem keyword_quote_outside : rejectedSyntax "local if" = true := by decide +kernel

-- Failure rolls back the complete input, but preserves earlier inputs.
private def started : Session := (Session.step {} (.assign "x" (.int 3))).session
private def failed : Session.Result := Session.step started
  (.seq (.assign "x" (.int 99)) (.binop .div (.int 1) (.int 0)))
theorem rollback : failed.outcome = .error .divByZero ∧
    failed.session.lookup "x" = some (.zz 3) ∧ failed.session.nextInput = 3 := by decide +kernel

end Macaulean.M2.LanguageReference
