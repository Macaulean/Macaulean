import Macaulean.Interpreter.GCD.Normalization
import Macaulean.Interpreter.GCD.Frames
import Macaulean.Verification.Fuel

/-!
Execution proofs for the checked-in source, using the actual lexical evaluator.
The source-shape equalities are checked by Lean's kernel against the compiled
library. The mathematical polynomial lemmas do not replace source execution.
-/
namespace Macaulean.M2.GCD.Execution
open Lexical Macaulean.M2.Runtime Univariate

set_option linter.unusedSimpArgs false

def localVar (i : Nat) : Code := .read (.slot 0 i)
def globalVar (name : String) : Code := .read (.global name)

def gcdBody : Code :=
  .ifElse (.binop .eq (localVar 1) (.int 0))
    (.ifElse (.binop .eq (localVar 0) (.int 0))
      (localVar 0)
      (.binop .div (localVar 0)
        (.apply (globalVar "leadCoefficient") (localVar 0))))
    (.apply (globalVar "m2gcdLoop") (.sequence [
      localVar 1,
      .apply (globalVar "normalForm") (.sequence [localVar 0, .listLit [localVar 1]])]))

theorem gcd_source :
    Library.lookup "m2gcdLoop" = some (.lambda (.fixed ["f","g"]) 2 gcdBody) := rfl

theorem allocated_read (s : State) (vs : List Value) (i : Nat) (v : Value)
    (hi : vs[i]? = some v) :
    readRef (.slot 0 i) [(s.allocate vs).1] (s.allocate vs).2 = .ok v := by
  have hbound : i < vs.length := (List.getElem?_eq_some_iff.mp hi).1
  simp [State.allocate, readRef, cellAt, List.getElem?_range hbound,
    List.getElem?_append_right, hi, bind, pure, Except.pure]

theorem allocated_global (s : State) (vs : List Value) (fs : Frames) (name : String)
    (v : Value) (h : s.env.lookup name = some v) :
    readRef (.global name) fs (s.allocate vs).2 = .ok v := by
  simp [readRef, State.allocate, h]

theorem library_call (fuel : Nat) (name : String) (params : Parameters)
    (slots : Nat) (body : Code) (arg : Value) (vs : List Value) (s : State)
    (hcode : Library.lookup name = some (.lambda params slots body))
    (ha : arguments params arg = .ok vs) :
    call (fuel+1) (.algebra (.library name)) arg s =
      catchReturn (eval fuel body
        [(s.allocate (vs ++ List.replicate (slots-vs.length) .null)).1]
        (s.allocate (vs ++ List.replicate (slots-vs.length) .null)).2) := by
  simp [call, hcode, ha, liftResult, Except.mapError, bind, Except.bind]

theorem builtin_call (fuel : Nat) (p : Polynomials.Primitive) (arg v : Value)
    (s : State) (h : Polynomials.callPrimitive p arg = .ok v) :
    call (fuel+1) (.algebra (.builtin p)) arg s = .ok (v,s) := by
  simp [call, h, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem gcd_both_zero (fuel id : Nat) (name : String) (s : State) :
    call (fuel+10) (.algebra (.library "m2gcdLoop"))
      (.sequence [value id name ⟨[]⟩, value id name ⟨[]⟩]) s =
      .ok (value id name ⟨[]⟩,
        (s.allocate [value id name ⟨[]⟩, value id name ⟨[]⟩]).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s gcd_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  have h0 := allocated_read s [value id name ⟨[]⟩, value id name ⟨[]⟩]
    0 (value id name ⟨[]⟩) rfl
  have h1 := allocated_read s [value id name ⟨[]⟩, value id name ⟨[]⟩]
    1 (value id name ⟨[]⟩) rfl
  simp only [gcdBody, localVar, globalVar, eval, h0, h1,
    eval_eq_zero id name ⟨[]⟩ .nil, List.isEmpty_nil,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

theorem gcd_second_zero (fuel id : Nat) (name : String) (s : State)
    (t : Univariate.Term) (ts : List Univariate.Term) (hp : Canonical (t :: ts))
    (hglobal : s.env.lookup "leadCoefficient" =
      some (.algebra (.builtin .leadCoefficient))) :
    call (fuel+10) (.algebra (.library "m2gcdLoop"))
      (.sequence [value id name ⟨t :: ts⟩, value id name ⟨[]⟩]) s =
      .ok (value id name (monicNormalize ⟨t :: ts⟩),
        (s.allocate [value id name ⟨t :: ts⟩, value id name ⟨[]⟩]).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s gcd_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  have h0 := allocated_read s [value id name ⟨t :: ts⟩, value id name ⟨[]⟩]
    0 (value id name ⟨t :: ts⟩) rfl
  have h1 := allocated_read s [value id name ⟨t :: ts⟩, value id name ⟨[]⟩]
    1 (value id name ⟨[]⟩) rfl
  have hread : readRef (.global "leadCoefficient")
      [(s.allocate [value id name ⟨t :: ts⟩, value id name ⟨[]⟩]).1]
      (s.allocate [value id name ⟨t :: ts⟩, value id name ⟨[]⟩]).2 =
        .ok (.algebra (.builtin .leadCoefficient)) := by
    simp [readRef, State.allocate, hglobal]
  have hc := leading_coefficient id name t ts hp
  have hne := canonical_nonzero hp List.mem_cons_self
  simp only [gcdBody, localVar, globalVar, eval, h0, h1, hread,
    eval_eq_zero id name ⟨[]⟩ .nil, eval_eq_zero id name ⟨t :: ts⟩ hp,
    List.isEmpty_nil, List.isEmpty_cons,
    builtin_call _ _ _ _ _ hc, eval_div_scalar id name ⟨t :: ts⟩ t.coefficient hp hne,
    monicNormalize, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure,
    catchReturn]

def reducerBody : Code :=
  .ifElse (.binop .eq (localVar 2) (.unop .length (localVar 1)))
    (.unop .neg (.int 1))
    (.ifElse
      (.apply (globalVar "m2MonomialDivides") (.sequence [
        .apply (globalVar "leadMonomial")
          (.binop .index (.binop .index (localVar 1) (localVar 2)) (.int 0)),
        .apply (globalVar "leadMonomial") (localVar 0)]))
      (localVar 2)
      (.apply (globalVar "m2gbReducer")
        (.sequence [localVar 0, localVar 1, .binop .add (localVar 2) (.int 1)])))

theorem reducer_source :
    Library.lookup "m2gbReducer" =
      some (.lambda (.fixed ["h","G","j"]) 3 reducerBody) := rfl

/-- End-of-list selection returns -1 without consulting any polynomial data. -/
theorem reducer_end (fuel : Nat) (h : Value) (gs : List Value) (s : State) :
    call (fuel+10) (.algebra (.library "m2gbReducer"))
      (.sequence [h, .list gs, .zz gs.length]) s =
      .ok (.zz (-1), (s.allocate [h, .list gs, .zz gs.length]).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s reducer_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  have h1 := allocated_read s [h, .list gs, .zz gs.length] 1 (.list gs) rfl
  have h2 := allocated_read s [h, .list gs, .zz gs.length] 2 (.zz gs.length) rfl
  simp only [reducerBody, localVar, globalVar, eval, h1, h2,
    evalUnOp, evalBinOp, Value.toRat?, decide_true,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

def singletonDivisor (id : Nat) (name : String) (p : Poly) : Value :=
  .list [.list [value id name p, .list []]]

theorem index_zero (v : Value) (vs : List Value) :
    evalBinOp .index (.list (v :: vs)) (.zz 0) = .ok v := by
  simp [evalBinOp, indexValue, normalizedIndex]
  rfl

theorem length_list (vs : List Value) :
    evalUnOp .length (.list vs) = .ok (.zz vs.length) := rfl

theorem zero_ne_one :
    evalBinOp .eq (.zz 0) (.zz 1) = .ok (.bool false) := by decide +kernel

theorem zero_add_one :
    evalBinOp .add (.zz 0) (.zz 1) = .ok (.zz 1) := rfl

theorem reducer_divides (fuel id : Nat) (name : String) (s : State)
    (t u : Univariate.Term) (ts us : List Univariate.Term)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us))
    (hdegree : u.monomial.degree ≤ t.monomial.degree)
    (hglobalLead : s.env.lookup "leadMonomial" = some (.algebra (.builtin .leadMonomial)))
    (hglobalDiv : s.env.lookup "m2MonomialDivides" = some (.algebra (.builtin .monomialDivides))) :
    call (fuel+20) (.algebra (.library "m2gbReducer"))
      (.sequence [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, .zz 0]) s =
      .ok (.zz 0, (s.allocate
        [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, .zz 0]).2) := by
  rw [library_call (fuel+19) _ _ _ _ _ _ s reducer_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  let vs := [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, Value.zz 0]
  have h0 := allocated_read s vs 0 (value id name ⟨t :: ts⟩) rfl
  have h1 := allocated_read s vs 1 (singletonDivisor id name ⟨u :: us⟩) rfl
  have h2 := allocated_read s vs 2 (.zz 0) rfl
  have hl := allocated_global s vs [(s.allocate vs).1] _ _ hglobalLead
  have hd := allocated_global s vs [(s.allocate vs).1] _ _ hglobalDiv
  dsimp only [vs, singletonDivisor] at h0 h1 h2 hl hd
  have hpl := leading_monomial id name t ts hp
  have hgl := leading_monomial id name u us hg
  have hdiv := monomial_divides id name u.monomial.degree t.monomial.degree
  simp only [reducerBody, localVar, globalVar, eval, evalMany,
    h0, h1, h2, hl, hd, singletonDivisor, length_list, index_zero, zero_ne_one,
    List.length_cons, List.length_nil, Nat.reduceAdd, Int.ofNat_one,
    builtin_call _ _ _ _ _ hpl, builtin_call _ _ _ _ _ hgl,
    builtin_call _ _ _ _ _ hdiv, hdegree, decide_true, decide_false,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

theorem reducer_not_divides (fuel id : Nat) (name : String) (s : State)
    (t u : Univariate.Term) (ts us : List Univariate.Term)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us))
    (hdegree : ¬ u.monomial.degree ≤ t.monomial.degree)
    (hglobalLead : s.env.lookup "leadMonomial" = some (.algebra (.builtin .leadMonomial)))
    (hglobalDiv : s.env.lookup "m2MonomialDivides" = some (.algebra (.builtin .monomialDivides)))
    (hglobalRec : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer"))) :
    call (fuel+20) (.algebra (.library "m2gbReducer"))
      (.sequence [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, .zz 0]) s =
      .ok (.zz (-1), ((s.allocate
        [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, .zz 0]).2.allocate
        [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, .zz 1]).2) := by
  rw [library_call (fuel+19) _ _ _ _ _ _ s reducer_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  let vs := [value id name ⟨t :: ts⟩, singletonDivisor id name ⟨u :: us⟩, Value.zz 0]
  have h0 := allocated_read s vs 0 (value id name ⟨t :: ts⟩) rfl
  have h1 := allocated_read s vs 1 (singletonDivisor id name ⟨u :: us⟩) rfl
  have h2 := allocated_read s vs 2 (.zz 0) rfl
  have hl := allocated_global s vs [(s.allocate vs).1] _ _ hglobalLead
  have hd := allocated_global s vs [(s.allocate vs).1] _ _ hglobalDiv
  have hr := allocated_global s vs [(s.allocate vs).1] _ _ hglobalRec
  have hnext := reducer_end (fuel+6) (value id name ⟨t :: ts⟩)
    [.list [value id name ⟨u :: us⟩, .list []]] (s.allocate vs).2
  dsimp only [vs, singletonDivisor] at h0 h1 h2 hl hd hr hnext
  have hpl := leading_monomial id name t ts hp
  have hgl := leading_monomial id name u us hg
  have hdiv := monomial_divides id name u.monomial.degree t.monomial.degree
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Int.ofNat_one,
    Nat.add_assoc] at hnext
  simp only [reducerBody, localVar, globalVar, eval, evalMany,
    h0, h1, h2, hl, hd, hr, singletonDivisor, length_list, index_zero,
    zero_ne_one, zero_add_one, List.length_cons, List.length_nil, Nat.reduceAdd, Int.ofNat_one,
    builtin_call _ _ _ _ _ hpl, builtin_call _ _ _ _ _ hgl,
    builtin_call _ _ _ _ _ hdiv, hdegree, decide_true, decide_false, hnext,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

def subtractRowBody : Code :=
  .ifElse (.binop .eq (localVar 3) (.unop .length (localVar 0)))
    (.listLit [])
    (.binop .concat
      (.listLit [.binop .sub (.binop .index (localVar 0) (localVar 3))
        (.binop .mul (localVar 1) (.binop .index (localVar 2) (localVar 3)))])
      (.apply (globalVar "m2gbSubtractRow") (.sequence [
        localVar 0, localVar 1, localVar 2, .binop .add (localVar 3) (.int 1)])))

theorem subtract_row_source :
    Library.lookup "m2gbSubtractRow" =
      some (.lambda (.fixed ["row","c","other","i"]) 4 subtractRowBody) := rfl

theorem subtract_row_empty (fuel : Nat) (c : Value) (s : State) :
    call (fuel+10) (.algebra (.library "m2gbSubtractRow"))
      (.sequence [.list [],c,.list [],.zz 0]) s =
        .ok (.list [], (s.allocate [.list [],c,.list [],.zz 0]).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s subtract_row_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  have h0 := allocated_read s [.list [],c,.list [],.zz 0] 0 (.list []) rfl
  have h3 := allocated_read s [.list [],c,.list [],.zz 0] 3 (.zz 0) rfl
  have hz : evalBinOp .eq (.zz 0) (.zz 0) = .ok (.bool true) := by decide +kernel
  simp only [subtractRowBody, localVar, globalVar, eval, evalMany, h0, h3,
    length_list, List.length_nil, Int.ofNat_zero, hz,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

/-- The recursive branch calls the source normal form and then recurses on its
result. This is a compositional execution lemma, not an assumption that either
call succeeds universally. -/
theorem gcd_step (fuel id : Nat) (name : String) (s next after : State)
    (p : Poly) (u : Univariate.Term) (us : List Univariate.Term)
    (hg : Canonical (u :: us)) (remainder result : Value)
    (hglobalNF : s.env.lookup "normalForm" = some (.algebra (.library "normalForm")))
    (hglobalRec : s.env.lookup "m2gcdLoop" = some (.algebra (.library "m2gcdLoop")))
    (hnf : call (fuel+13) (.algebra (.library "normalForm"))
      (.sequence [value id name p, .list [value id name ⟨u :: us⟩]])
      (s.allocate [value id name p, value id name ⟨u :: us⟩]).2 =
      .ok (remainder,next))
    (hrec : call (fuel+17) (.algebra (.library "m2gcdLoop"))
      (.sequence [value id name ⟨u :: us⟩, remainder]) next = .ok (result,after)) :
    call (fuel+20) (.algebra (.library "m2gcdLoop"))
      (.sequence [value id name p, value id name ⟨u :: us⟩]) s = .ok (result,after) := by
  rw [library_call (fuel+19) _ _ _ _ _ _ s gcd_source (by rfl)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.sub_self,
    List.replicate_zero, List.append_nil]
  let vs := [value id name p, value id name ⟨u :: us⟩]
  have h0 := allocated_read s vs 0 (value id name p) rfl
  have h1 := allocated_read s vs 1 (value id name ⟨u :: us⟩) rfl
  have hn := allocated_global s vs [(s.allocate vs).1] _ _ hglobalNF
  have hr := allocated_global s vs [(s.allocate vs).1] _ _ hglobalRec
  dsimp only [vs] at h0 h1 hn hr
  have hz := eval_eq_zero id name ⟨u :: us⟩ hg
  simp only [List.isEmpty_cons] at hz
  simp only [gcdBody, localVar, globalVar, eval, evalMany, h0, h1, hn, hr, hz,
    hnf, hrec, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure,
    catchReturn]

end Macaulean.M2.GCD.Execution
