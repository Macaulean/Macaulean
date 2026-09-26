import Macaulean.Interpreter.Session

/-!
# Control-flow laws

The first laws describe the loop-free reference `evalTerm`, retained for proofs
about that fragment. Session laws use the lexical runtime actually run by the
worksheet. General resolved-runtime laws are in `Functions.lean`.
-/
namespace Macaulean.M2
namespace ControlFlow

theorem ifElse_true (c yes no : Term) (env env' : Env)
    (h : evalTerm c env = .ok (.bool true, env')) :
    evalTerm (.ifElse c yes no) env = evalTerm yes env' := by
  simp [evalTerm, h, bind, Except.bind]

theorem ifElse_false (c yes no : Term) (env env' : Env)
    (h : evalTerm c env = .ok (.bool false, env')) :
    evalTerm (.ifElse c yes no) env = evalTerm no env' := by
  simp [evalTerm, h, bind, Except.bind]

theorem ifThen_true (c yes : Term) (env env' : Env)
    (h : evalTerm c env = .ok (.bool true, env')) :
    evalTerm (.ifThen c yes) env = evalTerm yes env' := by
  simp [evalTerm, h, bind, Except.bind]

theorem ifThen_false (c yes : Term) (env env' : Env)
    (h : evalTerm c env = .ok (.bool false, env')) :
    evalTerm (.ifThen c yes) env = .ok (.null, env') := by
  simp [evalTerm, h, bind, Except.bind, pure, Except.pure]

theorem ifElse_condition_error (c yes no : Term) (env : Env) (err : Error)
    (h : evalTerm c env = .error err) :
    evalTerm (.ifElse c yes no) env = .error err := by
  simp [evalTerm, h, bind, Except.bind]

theorem ifThen_condition_error (c yes : Term) (env : Env) (err : Error)
    (h : evalTerm c env = .error err) :
    evalTerm (.ifThen c yes) env = .error err := by
  simp [evalTerm, h, bind, Except.bind]

theorem logic_short_circuit (op : LogicOp) (a skipped : Term) (env env' : Env)
    (h : evalTerm a env = .ok (.bool op.shortCircuit, env')) :
    evalTerm (.logic op a skipped) env = .ok (.bool op.shortCircuit, env') := by
  simp [evalTerm, h, bind, Except.bind, pure, Except.pure]

theorem and_continue (a b : Term) (env env' env'' : Env) (v : Bool)
    (ha : evalTerm a env = .ok (.bool true, env'))
    (hb : evalTerm b env' = .ok (.bool v, env'')) :
    evalTerm (.logic .andOp a b) env = .ok (.bool v, env'') := by
  simp [evalTerm, ha, hb, LogicOp.shortCircuit, evalLogicOp,
    bind, Except.bind, pure, Except.pure]

theorem or_continue (a b : Term) (env env' env'' : Env) (v : Bool)
    (ha : evalTerm a env = .ok (.bool false, env'))
    (hb : evalTerm b env' = .ok (.bool v, env'')) :
    evalTerm (.logic .orOp a b) env = .ok (.bool v, env'') := by
  simp [evalTerm, ha, hb, LogicOp.shortCircuit, evalLogicOp,
    bind, Except.bind, pure, Except.pure]

theorem logic_left_error (op : LogicOp) (a b : Term) (env : Env) (err : Error)
    (h : evalTerm a env = .error err) :
    evalTerm (.logic op a b) env = .error err := by
  simp [evalTerm, h, bind, Except.bind]

theorem block_continue (a b : Term) (env env' : Env) (v : Value)
    (h : evalTerm a env = .ok (v, env')) :
    evalTerm (.seq a b) env = evalTerm b env' := by
  simp [evalTerm, h, bind, Except.bind]

theorem block_error (a b : Term) (env : Env) (err : Error)
    (h : evalTerm a env = .error err) :
    evalTerm (.seq a b) env = .error err := by
  simp [evalTerm, h, bind, Except.bind]

theorem block_trailing_semicolon (a : Term) (env env' : Env) (v : Value)
    (h : evalTerm a env = .ok (v, env')) :
    evalTerm (.seq a .empty) env = .ok (.null, env') := by
  simp [evalTerm, h, bind, Except.bind]

/-- Successful null inputs commit the actual runtime environment. -/
theorem session_null_env (s : Session) (t : Term) (result : Runtime.InputResult)
    (h : s.evaluate t = .ok result) (hv : result.value = .null) :
    (s.step t).session.env = result.state.env := by
  simp [Session.step, h, hv]

/-- Failures preserve the previous global bindings; the heap is preserved as well. -/
theorem session_error_env (s : Session) (t : Term) (err : Error)
    (h : s.evaluate t = .error err) :
    (s.step t).session.env = s.env := by
  simp [Session.step, h]

end ControlFlow
end Macaulean.M2
