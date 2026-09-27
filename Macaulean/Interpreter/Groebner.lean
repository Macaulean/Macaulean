import Macaulean.Interpreter.Session

/-!
# Execution contracts for the source-language Groebner library

These laws describe dispatch, finite evaluation and transactional state. They
are not a universal proof of Buchberger termination or of the algebraic criterion.
The algorithm itself is the tracked `Buchberger.m2` file, not these theorems.
-/
namespace Macaulean.M2.Groebner
open Lexical

theorem gb_alias : Library.lookup "gb" = Library.lookup "m2gbMain" := rfl
theorem normalForm_alias : Library.lookup "normalForm" = Library.lookup "m2gbNormalForm" := rfl
theorem sPolynomial_alias : Library.lookup "sPolynomial" = Library.lookup "m2gbSPolynomial" := rfl

theorem call_zero (fn arg : Value) (s : Runtime.State) :
    Runtime.call 0 fn arg s = .error (.error .fuelExhausted) := rfl

theorem eval_zero (code : Code) (frames : Runtime.Frames) (s : Runtime.State) :
    Runtime.eval 0 code frames s = .error (.error .fuelExhausted) := rfl

/-- A library call runs the same lexical evaluator as an ordinary function body,
with a fresh frame, not the caller's lexical frame or a foreign engine. -/
theorem library_call (fuel : Nat) (name : String) (params : Parameters)
    (slots : Nat) (body : Code) (arg : Value) (values : List Value) (s : Runtime.State)
    (h : Library.lookup name = some (.lambda params slots body))
    (ha : Runtime.arguments params arg = .ok values) :
    Runtime.call (fuel+1) (.algebra (.library name)) arg s =
      let (frame,next) := s.allocate (values ++ List.replicate (slots-values.length) .null)
      Runtime.catchReturn (Runtime.eval fuel body [frame] next) := by
  simp [Runtime.call, h, ha, Runtime.liftResult, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- A basis remainder dispatches to the M2 library, not `divideByTerm`. -/
theorem remainder_dispatch (fuel : Nat) (a b : Code) (frames : Runtime.Frames)
    (s s1 s2 : Runtime.State) (v : Value) (r : Polynomials.RingInfo)
    (input gs : List Polynomials.Raw) (rows : List (List Polynomials.Raw))
    (ha : Runtime.eval fuel a frames s = .ok (v,s1))
    (hb : Runtime.eval fuel b frames s1 = .ok (.algebra (.basis r input gs rows),s2)) :
    Runtime.eval (fuel+1) (.binop .rem a b) frames s =
      Runtime.call fuel (.algebra (.library "normalForm"))
        (.sequence [v,.algebra (.basis r input gs rows)]) s2 := by
  simp [Runtime.eval, ha, hb, bind, Except.bind, pure, Except.pure]

theorem linearCombination_empty (n : Nat) :
    Polynomials.linearCombination n [] [] = .ok [] := rfl

theorem linearCombination_rejects_dimension (n : Nat) (a b : List Polynomials.Raw)
    (h : a.length ≠ b.length) :
    Polynomials.linearCombination n a b =
      .error (.algebra "coefficient row has the wrong dimension") := by
  simp [Polynomials.linearCombination, h]

/-- A failed computation cannot publish a partial basis, changed cells, or a
fresh ring. Previous successful worksheet inputs are preserved. -/
theorem failed_input_rolls_back (s : Session) (t : Term) (fuel : Nat) (e : Error)
    (h : s.evaluate t fuel = .error e) :
    (s.step t false fuel).session.env = s.env ∧
    (s.step t false fuel).session.heap = s.heap ∧
    (s.step t false fuel).session.scope = s.scope ∧
    (s.step t false fuel).session.fileFrame = s.fileFrame := by
  simp [Session.step, h]

theorem failed_input_has_no_output (s : Session) (t : Term) (fuel : Nat) (e : Error)
    (h : s.evaluate t fuel = .error e) :
    (s.step t false fuel).output = none := by
  simp [Session.step, h]
end Macaulean.M2.Groebner
