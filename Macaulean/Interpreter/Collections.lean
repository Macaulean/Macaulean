import Lean
import Macaulean.Interpreter.Session

/-!
# Immutable collection laws

These laws apply to arbitrary element expressions and environments. They state
left-to-right evaluation, error propagation, cardinalities, checked indexing,
and the impossibility of a successful indexed mutation. No oracle is used.
-/
namespace Macaulean.M2.Collections

theorem evalTerms_nil (env : Env) : evalTerms [] env = .ok ([], env) := rfl

theorem evalTerms_cons (t : Term) (ts : List Term) (env mid final : Env)
    (v : Value) (vs : List Value)
    (ht : evalTerm t env = .ok (v, mid))
    (hs : evalTerms ts mid = .ok (vs, final)) :
    evalTerms (t :: ts) env = .ok (v :: vs, final) := by
  simp [evalTerms, ht, hs, bind, Except.bind, pure, Except.pure]

theorem evalTerms_head_error (t : Term) (ts : List Term) (env : Env) (e : Error)
    (h : evalTerm t env = .error e) : evalTerms (t :: ts) env = .error e := by
  simp [evalTerms, h, bind, Except.bind]

theorem evalTerms_tail_error (t : Term) (ts : List Term) (env mid : Env)
    (v : Value) (e : Error) (ht : evalTerm t env = .ok (v, mid))
    (hs : evalTerms ts mid = .error e) : evalTerms (t :: ts) env = .error e := by
  simp [evalTerms, ht, hs, bind, Except.bind]

theorem list_literal (ts : List Term) (env final : Env) (vs : List Value)
    (h : evalTerms ts env = .ok (vs, final)) :
    evalTerm (.listLit ts) env = .ok (.list vs, final) := by
  simp [evalTerm, h, bind, Except.bind, pure, Except.pure]

theorem sequence_literal (ts : List Term) (env final : Env) (vs : List Value)
    (h : evalTerms ts env = .ok (vs, final)) :
    evalTerm (.sequence ts) env = .ok (.sequence vs, final) := by
  simp [evalTerm, h, bind, Except.bind, pure, Except.pure]

theorem list_literal_error (ts : List Term) (env : Env) (e : Error)
    (h : evalTerms ts env = .error e) : evalTerm (.listLit ts) env = .error e := by
  simp [evalTerm, h, bind, Except.bind]

theorem sequence_literal_error (ts : List Term) (env : Env) (e : Error)
    (h : evalTerms ts env = .error e) : evalTerm (.sequence ts) env = .error e := by
  simp [evalTerm, h, bind, Except.bind]

theorem list_length (xs : List Value) : evalUnOp .length (.list xs) = .ok (.zz xs.length) := rfl

theorem sequence_length (xs : List Value) : evalUnOp .length (.sequence xs) = .ok (.zz xs.length) := rfl

theorem range_length (first : Int) (count : Nat) : (rangeValues first count).length = count := by
  simp [rangeValues]

theorem list_concat (xs ys : List Value) :
    evalBinOp .concat (.list xs) (.list ys) = .ok (.list (xs ++ ys)) := rfl

theorem sequence_concat (xs ys : List Value) :
    evalBinOp .concat (.sequence xs) (.sequence ys) = .ok (.sequence (xs ++ ys)) := rfl

theorem concat_length (xs ys : List Value) : (xs ++ ys).length = xs.length + ys.length := by
  simp

/-- Repetition evaluates its argument exactly once, even if the result is empty. -/
theorem repetition_once (count element : Term) (env mid final : Env) (n : Int) (v : Value)
    (hn : evalTerm count env = .ok (.zz n, mid))
    (hv : evalTerm element mid = .ok (v, final)) :
    evalTerm (.binop .repeat count element) env =
      .ok (.sequence (List.replicate n.toNat v), final) := by
  simp [evalTerm, hn, hv, evalBinOp, bind, Except.bind, pure, Except.pure]

theorem repetition_length (n : Nat) (v : Value) : (List.replicate n v).length = n := by simp

theorem normalizedIndex_nonnegative (n i : Nat) (h : i < n) :
    normalizedIndex n (Int.ofNat i) = some i := by
  have h0 : ¬ Int.ofNat i < 0 := by omega
  have hb : 0 ≤ Int.ofNat i ∧ Int.ofNat i < Int.ofNat n := by omega
  simp only [normalizedIndex, if_neg h0, if_pos hb]

/-- A returned index is always in bounds, including normalization of negative indices. -/
theorem normalizedIndex_bounds (n : Nat) (i : Int) (j : Nat)
    (h : normalizedIndex n i = some j) : j < n := by
  let k := if i < 0 then i + (n : Int) else i
  change (if 0 ≤ k ∧ k < (n : Int) then some k.toNat else none) = some j at h
  by_cases valid : 0 ≤ k ∧ k < (n : Int)
  · simp only [if_pos valid] at h
    have hj := Option.some.inj h
    omega
  · simp only [if_neg valid] at h
    cases h

theorem indexValue_success (xs : List Value) (i : Int) (j : Nat) (v : Value)
    (hn : normalizedIndex xs.length i = some j) (hv : xs[j]? = some v) :
    indexValue xs i = .ok v := by simp [indexValue, hn, hv, pure, Except.pure]

theorem indexValue_error (xs : List Value) (i : Int)
    (h : normalizedIndex xs.length i = none) :
    indexValue xs i = .error (.indexOutOfBounds i xs.length) := by
  simp [indexValue, h]

/-- No indexed assignment in the immutable fragment can yield a successful value. -/
theorem indexed_assignment_ne_ok (a i rhs : Term) (env final : Env) (v : Value) :
    evalTerm (.indexAssign a i rhs) env ≠ .ok (v, final) := by
  cases ha : evalTerm a env with
  | error e => simp [evalTerm, ha, bind, Except.bind]
  | ok av =>
    rcases av with ⟨av, ea⟩
    cases hi : evalTerm i ea with
    | error e => simp [evalTerm, ha, hi, bind, Except.bind]
    | ok iv =>
      rcases iv with ⟨iv, ei⟩
      cases hv : evalTerm rhs ei with
      | error e => simp [evalTerm, ha, hi, hv, bind, Except.bind]
      | ok rv =>
        rcases rv with ⟨rv, er⟩
        cases av <;> simp [evalTerm, ha, hi, hv, bind, Except.bind]

end Macaulean.M2.Collections
