import Macaulean.Interpreter.GCD.BarePairs

namespace Macaulean.M2.GCD.Execution
open Lexical Macaulean.M2.Runtime Univariate
set_option linter.unusedSimpArgs false

structure NormalFormGlobals (s : State) : Prop extends ReductionGlobals s where
  data : s.env.lookup "m2NormalFormData" = some (.algebra (.builtin .normalFormData))
  ring : s.env.lookup "ring" = some (.algebra (.builtin .ring))
  promote : s.env.lookup "promote" = some (.algebra (.builtin .promote))
  bare : s.env.lookup "m2gbBarePairs" = some (.algebra (.library "m2gbBarePairs"))

def normalFormResult : Code :=
  .binop .index
    (.apply (globalVar "m2gbReduce") (.sequence [
      localVar 3,.listLit [],
      .apply (globalVar "m2gbBarePairs") (.sequence [
        localVar 4,.apply (globalVar "ring") (localVar 3),.int 0]),
      .binop .mul (.int 0) (localVar 3)])) (.int 0)

def normalFormBody : Code :=
  .seq (.set (.slot 0 2) (.apply (globalVar "m2NormalFormData")
    (.sequence [localVar 0,localVar 1])))
    (.seq (.set (.slot 0 3) (.binop .index (localVar 2) (.int 0)))
      (.seq (.set (.slot 0 4) (.binop .index (localVar 2) (.int 1))) normalFormResult))

theorem normal_form_source : Library.lookup "normalForm" =
    some (.lambda (.fixed ["f","G"]) 5 normalFormBody) := rfl

/-- Total correctness of the complete source normal-form wrapper on the inputs
used by GCD, including validation, divisor packaging and result extraction. -/
theorem normal_form_correct (fuel id : Nat) (name : String)
    (p : Poly) (u : Univariate.Term) (us : List Univariate.Term)
    (hp : Canonical p.terms) (hg : Canonical (u :: us))
    (s : State) (globals : NormalFormGlobals s)
    (hb : 64 * (rank p+1) ≤ fuel+94) :
    ∃ out after, Canonical out.terms ∧ Extends s after ∧
      Below u.monomial.degree out.terms ∧
      (∀ d, (Divides d ⟨u :: us⟩ ∧ Divides d out) ↔
        (Divides d p ∧ Divides d ⟨u :: us⟩)) ∧
      call (fuel+100) (.algebra (.library "normalForm"))
        (.sequence [value id name p,.list [value id name ⟨u :: us⟩]]) s =
        .ok (value id name out,after) := by
  let gv := value id name ⟨u :: us⟩
  let pv := value id name p
  let data := Value.list [pv,.list [gv]]
  let vs := [pv,Value.list [gv],.null,.null,.null]
  have hf := allocated_frame s vs
  obtain ⟨s2, hw2, hf2⟩ := hf.write 2 data (by simp [vs])
  obtain ⟨s3, hw3, hf3⟩ := hf2.write 3 pv (by simp [vs])
  obtain ⟨s4, hw4, hf4⟩ := hf3.write 4 (.list [gv]) (by simp [vs])
  obtain ⟨s5, he5, hbare⟩ := bare_pairs_singleton (fuel+49) id name s4 u us hg
    (by simpa only [hf4.env] using globals.promote)
    (by simpa only [hf4.env] using globals.bare)
  have hf5 := hf4.after_call he5
  obtain ⟨out,after,ho,he,hd,hdiv,hreduce⟩ := reduction_correct id name p u us hp hg
    s5 (globals.toReductionGlobals.of_extends hf5.extends) (fuel+94) hb
  refine ⟨out,after,ho,hf5.extends.trans he,hd,hdiv,?_⟩
  have h0 := allocated_read s vs 0 pv rfl
  have h1 := allocated_read s vs 1 (.list [gv]) rfl
  have hs2 := hf2.read 2 data (by simp [vs])
  have hs3 := hf3.read 2 data (by simp [vs])
  have h4p := hf4.read 3 pv (by simp [vs])
  have h4g := hf4.read 4 (.list [gv]) (by simp [vs])
  have h5p := hf5.read 3 pv (by simp [vs])
  change readRef (.slot 0 2) [(s.allocate vs).1] s2 = .ok data at hs2
  change readRef (.slot 0 2) [(s.allocate vs).1] s3 = .ok data at hs3
  change readRef (.slot 0 3) [(s.allocate vs).1] s4 = .ok pv at h4p
  change readRef (.slot 0 4) [(s.allocate vs).1] s4 = .ok (.list [gv]) at h4g
  change readRef (.slot 0 3) [(s.allocate vs).1] s5 = .ok pv at h5p
  change writeRef (.slot 0 2) data [(s.allocate vs).1] (s.allocate vs).2 = .ok s2 at hw2
  change writeRef (.slot 0 3) pv [(s.allocate vs).1] s2 = .ok s3 at hw3
  change writeRef (.slot 0 4) (.list [gv]) [(s.allocate vs).1] s3 = .ok s4 at hw4
  have gd := allocated_global s vs [(s.allocate vs).1] _ _ globals.data
  have gr : readRef (.global "ring") [(s.allocate vs).1] s4 = .ok (.algebra (.builtin .ring)) := by
    simp [readRef, hf4.env, globals.ring]
  have gb : readRef (.global "m2gbBarePairs") [(s.allocate vs).1] s4 =
      .ok (.algebra (.library "m2gbBarePairs")) := by simp [readRef, hf4.env, globals.bare]
  have gg : readRef (.global "m2gbReduce") [(s.allocate vs).1] s4 =
      .ok (.algebra (.library "m2gbReduce")) := by simp [readRef, hf4.env, globals.reduce]
  have hpdata := normal_form_data id name p ⟨u :: us⟩ hp hg
  change Polynomials.callPrimitive .normalFormData (.sequence [pv,.list [gv]]) = .ok data at hpdata
  have hpring := polynomial_ring id name p
  change Polynomials.callPrimitive .ring pv = .ok (ringValue id name) at hpring
  have hpzero := zero_mul_polynomial id name p hp
  change evalBinOp .mul (.zz 0) pv = .ok (value id name ⟨[]⟩) at hpzero
  change call (fuel+94) (.algebra (.library "m2gbReduce"))
    (.sequence [pv,.list [],singletonDivisor id name ⟨u :: us⟩,value id name ⟨[]⟩]) s5 =
    .ok (.list [value id name out,.list []],after) at hreduce
  have hbare' : call (fuel+89) (.algebra (.library "m2gbBarePairs"))
      (.sequence [.list [gv],ringValue id name,.zz 0]) s4 =
      .ok (singletonDivisor id name ⟨u :: us⟩,s5) := by simpa [Nat.add_assoc, gv] using hbare
  have hset2 : eval (fuel+98) (.set (.slot 0 2) (.apply (globalVar "m2NormalFormData")
      (.sequence [localVar 0,localVar 1]))) [(s.allocate vs).1] (s.allocate vs).2 = .ok (data,s2) := by
    simp only [eval, evalMany, localVar, globalVar, checkWritable, h0, h1, gd,
      builtin_call _ _ _ _ _ hpdata, hw2, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  have hset3 : eval (fuel+97) (.set (.slot 0 3) (.binop .index (localVar 2) (.int 0)))
      [(s.allocate vs).1] s2 = .ok (pv,s3) := by
    simp only [eval, localVar, checkWritable, hs2, data, index_zero, hw3,
      liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  have hset4 : eval (fuel+96) (.set (.slot 0 4) (.binop .index (localVar 2) (.int 1)))
      [(s.allocate vs).1] s3 = .ok (.list [gv],s4) := by
    simp only [eval, localVar, checkWritable, hs3, data, index_one_pair, hw4,
      liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  have hfinal : eval (fuel+96) normalFormResult [(s.allocate vs).1] s4 =
      .ok (value id name out,after) := by
    simp only [normalFormResult, eval, evalMany, localVar, globalVar,
      h4p, h4g, h5p, gr, gb, gg, builtin_call _ _ _ _ _ hpring,
      hbare', hpzero, hreduce, index_zero,
      liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
  rw [library_call (fuel+99) _ _ _ _ _ _ s normal_form_source (by rfl)]
  change catchReturn (eval (fuel+99) normalFormBody [(s.allocate vs).1] (s.allocate vs).2) = _
  unfold normalFormBody
  rw [eval]
  simp only [hset2, bind, Except.bind]
  rw [eval]
  simp only [hset3, bind, Except.bind]
  rw [eval]
  simp only [hset4, hfinal, bind, Except.bind, catchReturn]

end Macaulean.M2.GCD.Execution
