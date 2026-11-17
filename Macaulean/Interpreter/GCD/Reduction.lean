import Macaulean.Interpreter.GCD.Execution

/-! Execution of the actual normal-form reduction used by the GCD source. -/
namespace Macaulean.M2.GCD.Execution
open Lexical Macaulean.M2.Runtime Univariate
set_option linter.unusedSimpArgs false

def reductionMoveHead : Code :=
  .seq (.set (.slot 0 5) (.apply (globalVar "leadTerm") (localVar 0)))
    (.apply (globalVar "m2gbReduce") (.sequence [
      .binop .sub (localVar 0) (localVar 5), localVar 1, localVar 2,
      .binop .add (localVar 3) (localVar 5)]))

def reductionCoefficient : Code :=
  .binop .mul
    (.binop .div
      (.apply (globalVar "leadCoefficient") (localVar 0))
      (.apply (globalVar "leadCoefficient") (.binop .index (localVar 6) (.int 0))))
    (.apply (globalVar "m2MonomialQuotient") (.sequence [
      .apply (globalVar "leadMonomial") (localVar 0),
      .apply (globalVar "leadMonomial") (.binop .index (localVar 6) (.int 0))]))

def reductionCancelRecurse : Code :=
  .apply (globalVar "m2gbReduce") (.sequence [
    .binop .sub (localVar 0)
      (.binop .mul (localVar 7) (.binop .index (localVar 6) (.int 0))),
    .apply (globalVar "m2gbSubtractRow") (.sequence [
      localVar 1, localVar 7, .binop .index (localVar 6) (.int 1), .int 0]),
    localVar 2, localVar 3])

def reductionCancel : Code :=
  .seq (.set (.slot 0 6) (.binop .index (localVar 2) (localVar 4)))
    (.seq (.set (.slot 0 7) reductionCoefficient) reductionCancelRecurse)

def reductionBody : Code :=
  .ifElse (.binop .eq (localVar 0) (.int 0))
    (.listLit [localVar 3, localVar 1])
    (.seq (.set (.slot 0 4) (.apply (globalVar "m2gbReducer")
      (.sequence [localVar 0,localVar 2,.int 0])))
      (.ifElse (.binop .lt (localVar 4) (.int 0)) reductionMoveHead reductionCancel))

theorem reduction_source : Library.lookup "m2gbReduce" =
    some (.lambda (.fixed ["h","row","G","remainder"]) 8 reductionBody) := rfl

def reductionLocals (h row gs remainder : Value) : List Value :=
  [h,row,gs,remainder,.null,.null,.null,.null]

theorem reduction_zero (fuel id : Nat) (name : String) (row gs remainder : Value)
    (s : State) :
    call (fuel+10) (.algebra (.library "m2gbReduce"))
      (.sequence [value id name ⟨[]⟩, row,gs,remainder]) s =
        .ok (.list [remainder,row],
          (s.allocate (reductionLocals (value id name ⟨[]⟩) row gs remainder)).2) := by
  rw [library_call (fuel+9) _ _ _ _ _ _ s reduction_source (by rfl)]
  change catchReturn (eval (fuel+9) reductionBody
    [(s.allocate (reductionLocals (value id name ⟨[]⟩) row gs remainder)).1]
    (s.allocate (reductionLocals (value id name ⟨[]⟩) row gs remainder)).2) = _
  have h0 := allocated_read s (reductionLocals (value id name ⟨[]⟩) row gs remainder)
    0 (value id name ⟨[]⟩) rfl
  have h1 := allocated_read s (reductionLocals (value id name ⟨[]⟩) row gs remainder) 1 row rfl
  have h3 := allocated_read s (reductionLocals (value id name ⟨[]⟩) row gs remainder) 3 remainder rfl
  have hz := eval_eq_zero id name ⟨[]⟩ .nil
  simp only [List.isEmpty_nil] at hz
  simp only [reductionBody, localVar, eval, evalMany, h0, h1, h3, hz,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

theorem reduction_move_head (fuel id : Nat) (name : String)
    (parent s next after : State) (t : Univariate.Term) (ts : List Univariate.Term)
    (r : Poly) (row gs j oldTerm divisor coefficient result : Value)
    (hp : Canonical (t :: ts)) (hr : Canonical r.terms)
    (hf : InFrame parent
      [value id name ⟨t :: ts⟩,row,gs,value id name r,j,oldTerm,divisor,coefficient] s)
    (hlead : parent.env.lookup "leadTerm" = some (.algebra (.builtin .leadTerm)))
    (hrecurse : parent.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce")))
    (hw : writeRef (.slot 0 5) (value id name ⟨[t]⟩) [frame parent 8] s = .ok next)
    (hrec : call (fuel+18) (.algebra (.library "m2gbReduce"))
      (.sequence [value id name ⟨ts⟩,row,gs,
        value id name (KernelPolynomial.add r ⟨[t]⟩)]) next = .ok (result,after)) :
    eval (fuel+20) reductionMoveHead [frame parent 8] s = .ok (result,after) := by
  have hf' := hf.write_result 5 (value id name ⟨[t]⟩) (by simp) hw
  have h0 := hf.read 0 (value id name ⟨t :: ts⟩) rfl
  have hn0 := hf'.read 0 (value id name ⟨t :: ts⟩) rfl
  have hn1 := hf'.read 1 row rfl
  have hn2 := hf'.read 2 gs rfl
  have hn3 := hf'.read 3 (value id name r) rfl
  have hn5 := hf'.read 5 (value id name ⟨[t]⟩) rfl
  simp only [List.length_cons, List.length_nil, List.length_set] at h0 hn0 hn1 hn2 hn3 hn5
  have hl : readRef (.global "leadTerm") [frame parent 8] s =
      .ok (.algebra (.builtin .leadTerm)) := by simp [readRef, hf.env, hlead]
  have hc : readRef (.global "m2gbReduce") [frame parent 8] next =
      .ok (.algebra (.library "m2gbReduce")) := by simp [readRef, hf'.env, hrecurse]
  have hterm := leading_term id name t ts hp
  have hsingle : Canonical [t] := .cons (canonical_nonzero hp List.mem_cons_self) (below_nil _) .nil
  have hsub := eval_sub id name ⟨t :: ts⟩ ⟨[t]⟩ hp hsingle
  rw [sub_head hp] at hsub
  have hadd := eval_add id name r ⟨[t]⟩ hr hsingle
  simp only [reductionMoveHead, localVar, globalVar, eval, evalMany,
    checkWritable, h0, hn0, hn1, hn2, hn3, hn5, hl, hc,
    builtin_call _ _ _ _ _ hterm, hw, hsub, hadd, hrec,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem reduction_coefficient (fuel id : Nat) (name : String) (s : State) (fs : Frames)
    (t u : Univariate.Term) (ts us : List Univariate.Term) (row : Value)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us))
    (hdegree : u.monomial.degree ≤ t.monomial.degree)
    (h0 : readRef (.slot 0 0) fs s = .ok (value id name ⟨t :: ts⟩))
    (h6 : readRef (.slot 0 6) fs s = .ok (.list [value id name ⟨u :: us⟩,row]))
    (hlc : s.env.lookup "leadCoefficient" = some (.algebra (.builtin .leadCoefficient)))
    (hlm : s.env.lookup "leadMonomial" = some (.algebra (.builtin .leadMonomial)))
    (hmq : s.env.lookup "m2MonomialQuotient" = some (.algebra (.builtin .monomialQuotient))) :
    eval (fuel+20) reductionCoefficient fs s =
      .ok (value id name (cancellationTerm t u),s) := by
  have ht := canonical_nonzero hp List.mem_cons_self
  have hu := canonical_nonzero hg List.mem_cons_self
  have hratio : t.coefficient / u.coefficient ≠ 0 := by
    intro hz
    have he := Rat.div_mul_cancel (a := t.coefficient) hu
    rw [hz, Rat.zero_mul] at he
    exact ht he.symm
  have hc0 := leading_coefficient id name t ts hp
  have hc6 := leading_coefficient id name u us hg
  have hm0 := leading_monomial id name t ts hp
  have hm6 := leading_monomial id name u us hg
  have hq := monomial_quotient id name t.monomial.degree u.monomial.degree hdegree
  have hd := scalar_div t.coefficient u.coefficient hu
  have hm := eval_mul_scalar_monomial id name _ (t.monomial.degree-u.monomial.degree) hratio
  have glc : readRef (.global "leadCoefficient") fs s = .ok (.algebra (.builtin .leadCoefficient)) := by
    simp [readRef, hlc]
  have glm : readRef (.global "leadMonomial") fs s = .ok (.algebra (.builtin .leadMonomial)) := by
    simp [readRef, hlm]
  have gmq : readRef (.global "m2MonomialQuotient") fs s = .ok (.algebra (.builtin .monomialQuotient)) := by
    simp [readRef, hmq]
  simp only [reductionCoefficient, localVar, globalVar, eval, evalMany, h0, h6,
    glc, glm, gmq, index_zero,
    builtin_call _ _ _ _ _ hc0, builtin_call _ _ _ _ _ hc6,
    builtin_call _ _ _ _ _ hm0, builtin_call _ _ _ _ _ hm6,
    builtin_call _ _ _ _ _ hq, hd, hm, cancellationTerm,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

def emptyRowAfter (s : State) (c : Value) : State :=
  (s.allocate [.list [],c,.list [],.zz 0]).2

theorem index_one_pair (a b : Value) :
    evalBinOp .index (.list [a,b]) (.zz 1) = .ok b := by
  simp [evalBinOp, indexValue, normalizedIndex]
  rfl

theorem reduction_cancel_recurse (fuel id : Nat) (name : String)
    (parent s after : State) (t u : Univariate.Term) (ts us : List Univariate.Term)
    (gs remainder j oldTerm result : Value)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us))
    (hf : InFrame parent
      [value id name ⟨t :: ts⟩,.list [],gs,remainder,j,oldTerm,
        .list [value id name ⟨u :: us⟩,.list []],value id name (cancellationTerm t u)] s)
    (hrow : parent.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")))
    (hrecurse : parent.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce")))
    (hrec : call (fuel+19) (.algebra (.library "m2gbReduce"))
      (.sequence [
        value id name (KernelPolynomial.sub ⟨t :: ts⟩
          (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)),
        .list [],gs,remainder]) (emptyRowAfter s (value id name (cancellationTerm t u))) =
        .ok (result,after)) :
    eval (fuel+20) reductionCancelRecurse [frame parent 8] s = .ok (result,after) := by
  have h0 := hf.read 0 (value id name ⟨t :: ts⟩) rfl
  have h1 := hf.read 1 (.list []) rfl
  have h6 := hf.read 6 (.list [value id name ⟨u :: us⟩,.list []]) rfl
  have h7 := hf.read 7 (value id name (cancellationTerm t u)) rfl
  have hn := hf.after_call (allocate_extends s [.list [],value id name (cancellationTerm t u),.list [],.zz 0])
  have hn2 := hn.read 2 gs rfl
  have hn3 := hn.read 3 remainder rfl
  simp only [List.length_cons, List.length_nil] at h0 h1 h6 h7 hn2 hn3
  have gr : readRef (.global "m2gbSubtractRow") [frame parent 8] s =
      .ok (.algebra (.library "m2gbSubtractRow")) := by simp [readRef, hf.env, hrow]
  have gc : readRef (.global "m2gbReduce") [frame parent 8] s =
      .ok (.algebra (.library "m2gbReduce")) := by simp [readRef, hf.env, hrecurse]
  have hc := cancellationTerm_canonical (canonical_nonzero hp List.mem_cons_self)
    (canonical_nonzero hg List.mem_cons_self)
  have hm := eval_mul id name (cancellationTerm t u) ⟨u :: us⟩ hc hg
  have hs := eval_sub id name ⟨t :: ts⟩
    (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩) hp (mul_canonical ..)
  have hrowcall := subtract_row_empty (fuel+5) (value id name (cancellationTerm t u)) s
  simp only [Nat.add_assoc, Nat.reduceAdd] at hrowcall
  dsimp only [emptyRowAfter] at hrec
  simp only [reductionCancelRecurse, localVar, globalVar, eval, evalMany,
    h0, h1, h6, h7, hn2, hn3, gr, gc, index_zero, index_one_pair,
    hm, hs, hrowcall, hrec,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem reduction_cancel (fuel id : Nat) (name : String)
    (parent s selected next after : State) (t u : Univariate.Term)
    (ts us : List Univariate.Term) (remainder oldTerm oldDivisor oldCoefficient result : Value)
    (hp : Canonical (t :: ts)) (hg : Canonical (u :: us))
    (hdegree : u.monomial.degree ≤ t.monomial.degree)
    (hf : InFrame parent
      [value id name ⟨t :: ts⟩,.list [],singletonDivisor id name ⟨u :: us⟩,
        remainder,.zz 0,oldTerm,oldDivisor,oldCoefficient] s)
    (hlc : parent.env.lookup "leadCoefficient" = some (.algebra (.builtin .leadCoefficient)))
    (hlm : parent.env.lookup "leadMonomial" = some (.algebra (.builtin .leadMonomial)))
    (hmq : parent.env.lookup "m2MonomialQuotient" = some (.algebra (.builtin .monomialQuotient)))
    (hrow : parent.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")))
    (hrecurse : parent.env.lookup "m2gbReduce" = some (.algebra (.library "m2gbReduce")))
    (hw6 : writeRef (.slot 0 6) (.list [value id name ⟨u :: us⟩,.list []])
      [frame parent 8] s = .ok selected)
    (hw7 : writeRef (.slot 0 7) (value id name (cancellationTerm t u))
      [frame parent 8] selected = .ok next)
    (hrec : call (fuel+27) (.algebra (.library "m2gbReduce"))
      (.sequence [
        value id name (KernelPolynomial.sub ⟨t :: ts⟩
          (KernelPolynomial.mul (cancellationTerm t u) ⟨u :: us⟩)),
        .list [],singletonDivisor id name ⟨u :: us⟩,remainder])
      (emptyRowAfter next (value id name (cancellationTerm t u))) = .ok (result,after)) :
    eval (fuel+30) reductionCancel [frame parent 8] s = .ok (result,after) := by
  have hf6 := hf.write_result 6 (.list [value id name ⟨u :: us⟩,.list []]) (by simp) hw6
  have hf7 := hf6.write_result 7 (value id name (cancellationTerm t u)) (by simp) hw7
  have h2 := hf.read 2 (singletonDivisor id name ⟨u :: us⟩) rfl
  have h4 := hf.read 4 (.zz 0) rfl
  have hs0 := hf6.read 0 (value id name ⟨t :: ts⟩) rfl
  have hs6 := hf6.read 6 (.list [value id name ⟨u :: us⟩,.list []]) rfl
  simp only [List.length_cons, List.length_nil, List.length_set] at h2 h4 hs0 hs6
  have hcoef := reduction_coefficient (fuel+7) id name selected [frame parent 8]
    t u ts us (.list []) hp hg hdegree hs0 hs6
    (by simpa [hf6.env] using hlc) (by simpa [hf6.env] using hlm)
    (by simpa [hf6.env] using hmq)
  have htail := reduction_cancel_recurse (fuel+8) id name parent next after
    t u ts us (singletonDivisor id name ⟨u :: us⟩) remainder (.zz 0) oldTerm result
    hp hg hf7 hrow hrecurse (by simpa [Nat.add_assoc] using hrec)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hcoef htail
  have hset6 : eval (fuel+29)
      (.set (.slot 0 6) (.binop .index (localVar 2) (localVar 4))) [frame parent 8] s =
      .ok (.list [value id name ⟨u :: us⟩,.list []],selected) := by
    simp only [eval, localVar, checkWritable, h2, h4, singletonDivisor,
      index_zero, hw6, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  have hset7 : eval (fuel+28) (.set (.slot 0 7) reductionCoefficient)
      [frame parent 8] selected = .ok (value id name (cancellationTerm t u),next) := by
    rw [eval]
    simp only [checkWritable, hcoef, hw7, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  unfold reductionCancel
  rw [eval]
  simp only [hset6, bind, Except.bind]
  rw [eval]
  simp only [hset7, htail, bind, Except.bind]


theorem reduction_dispatch (fuel id : Nat) (name : String)
    (s selected next after : State) (t : Univariate.Term) (ts : List Univariate.Term)
    (row gs remainder j result : Value) (negative : Bool)
    (hp : Canonical (t :: ts))
    (hglobal : s.env.lookup "m2gbReducer" = some (.algebra (.library "m2gbReducer")))
    (hsel : call (fuel+35) (.algebra (.library "m2gbReducer"))
      (.sequence [value id name ⟨t :: ts⟩,gs,.zz 0])
      (s.allocate (reductionLocals (value id name ⟨t :: ts⟩) row gs remainder)).2 =
      .ok (j,selected))
    (hext : Extends
      (s.allocate (reductionLocals (value id name ⟨t :: ts⟩) row gs remainder)).2 selected)
    (hw : writeRef (.slot 0 4) j [frame s 8] selected = .ok next)
    (hcmp : evalBinOp .lt j (.zz 0) = .ok (.bool negative))
    (hbranch : eval (fuel+36)
      (if negative then reductionMoveHead else reductionCancel) [frame s 8] next =
      .ok (result,after)) :
    call (fuel+40) (.algebra (.library "m2gbReduce"))
      (.sequence [value id name ⟨t :: ts⟩,row,gs,remainder]) s = .ok (result,after) := by
  let vs := reductionLocals (value id name ⟨t :: ts⟩) row gs remainder
  have h0 := allocated_read s vs 0 (value id name ⟨t :: ts⟩) rfl
  have h2 := allocated_read s vs 2 gs rfl
  have hg := allocated_global s vs [(s.allocate vs).1] _ _ hglobal
  have hn := ((allocated_frame s vs).after_call hext).write_result 4 j (by simp [vs, reductionLocals]) hw
  have h4 := hn.read 4 j (by simp [vs, reductionLocals])
  change readRef (.slot 0 4) [frame s 8] next = .ok j at h4
  have hz := eval_eq_zero id name ⟨t :: ts⟩ hp
  simp only [List.isEmpty_cons] at hz
  have hchoose : eval (fuel+37)
      (.ifElse (.binop .lt (localVar 4) (.int 0)) reductionMoveHead reductionCancel)
      [frame s 8] next = .ok (result,after) := by
    rw [eval]
    have hcondition : eval (fuel+36) (.binop .lt (localVar 4) (.int 0))
        [frame s 8] next = .ok (.bool negative,next) := by
      simp only [eval, localVar, h4, hcmp, liftResult, Except.mapError,
        bind, Except.bind, pure, Except.pure]
    simp only [hcondition, bind, Except.bind]
    cases negative <;> exact hbranch
  rw [library_call (fuel+39) _ _ _ _ _ _ s reduction_source (by rfl)]
  change catchReturn (eval (fuel+39) reductionBody [(s.allocate vs).1] (s.allocate vs).2) = _
  change call (fuel+35) (.algebra (.library "m2gbReducer"))
    (.sequence [value id name ⟨t :: ts⟩,gs,.zz 0]) (s.allocate vs).2 = .ok (j,selected) at hsel
  change writeRef (.slot 0 4) j [(s.allocate vs).1] selected = .ok next at hw
  have hset : eval (fuel+37)
      (.set (.slot 0 4) (.apply (globalVar "m2gbReducer")
        (.sequence [localVar 0,localVar 2,.int 0])))
      [(s.allocate vs).1] (s.allocate vs).2 = .ok (j,next) := by
    simp only [eval, evalMany, localVar, globalVar, h0, h2, hg, checkWritable,
      hsel, hw, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  unfold reductionBody
  rw [eval]
  have hcondition : eval (fuel+38) (.binop .eq (localVar 0) (.int 0))
      [(s.allocate vs).1] (s.allocate vs).2 = .ok (.bool false,(s.allocate vs).2) := by
    simp only [eval, localVar, h0, hz, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  simp only [hcondition, bind, Except.bind]
  rw [eval]
  simp only [hset, bind, Except.bind]
  change catchReturn (eval (fuel+37) _ [frame s 8] next) = _
  rw [hchoose]
  rfl

end Macaulean.M2.GCD.Execution
