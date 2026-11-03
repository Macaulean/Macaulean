import Macaulean.Interpreter.GCD.LoopCorrectness

namespace Macaulean.M2.GCD.Execution
open Lexical Macaulean.M2.Runtime Univariate
set_option linter.unusedSimpArgs false

def gcdEntryBody : Code :=
  .seq (.set (.slot 0 1) (.apply (globalVar "m2GCDInputs") (localVar 0)))
    (.apply (globalVar "m2gcdLoop") (.sequence [
      .binop .index (localVar 1) (.int 0),.binop .index (localVar 1) (.int 1)]))

theorem gcd_entry_source : Library.lookup "gcd" =
    some (.lambda (.variadic "input") 2 gcdEntryBody) := rfl

theorem prelude_globals : GCDGlobals ({} : State) := by repeat constructor

theorem gcd_entry_step (fuel : Nat) (arg p g : Value) (s : State)
    (hdata : Polynomials.callPrimitive .gcdInputs arg = .ok (.list [p,g]))
    (hd : s.env.lookup "m2GCDInputs" = some (.algebra (.builtin .gcdInputs)))
    (hl : s.env.lookup "m2gcdLoop" = some (.algebra (.library "m2gcdLoop"))) :
    ∃ next, Extends s next ∧ ∀ result after,
      call (fuel+17) (.algebra (.library "m2gcdLoop")) (.sequence [p,g]) next = .ok (result,after) →
      call (fuel+20) (.algebra (.library "gcd")) arg s = .ok (result,after) := by
  let vs := [arg,Value.null]
  have hf := allocated_frame s vs
  obtain ⟨next, hw, hn⟩ := hf.write 1 (.list [p,g]) (by simp [vs])
  refine ⟨next,hn.extends,?_⟩
  intro result after hrec
  have h0 := allocated_read s vs 0 arg rfl
  have h1 := hn.read 1 (.list [p,g]) (by simp [vs])
  change readRef (.slot 0 1) [(s.allocate vs).1] next = .ok (.list [p,g]) at h1
  change writeRef (.slot 0 1) (.list [p,g]) [(s.allocate vs).1] (s.allocate vs).2 = .ok next at hw
  have gd := allocated_global s vs [(s.allocate vs).1] _ _ hd
  have gl : readRef (.global "m2gcdLoop") [(s.allocate vs).1] next =
      .ok (.algebra (.library "m2gcdLoop")) := by simp [readRef, hn.env, hl]
  rw [library_call (fuel+19) _ _ _ _ _ _ s gcd_entry_source (by rfl)]
  change catchReturn (eval (fuel+19) gcdEntryBody [(s.allocate vs).1] (s.allocate vs).2) = _
  simp only [gcdEntryBody, localVar, globalVar, eval, evalMany, checkWritable,
    h0, h1, gd, gl, builtin_call _ _ _ _ _ hdata, hw, index_zero, index_one_pair,
    hrec, liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

theorem gcd_inputs_canonical (id : Nat) (name : String) (p g : Poly)
    (hp : Canonical p.terms) (hg : Canonical g.terms) :
    Polynomials.gcdInputs (.sequence [value id name p,value id name g]) =
      .ok (ringInfo id name,Polynomials.encode p,Polynomials.encode g) := by
  simp [Polynomials.gcdInputs, Polynomials.binaryArgs, Polynomials.unpack,
    as_polynomial id name p hp, as_polynomial id name g hg, ringInfo,
    bind, Except.bind, pure, Except.pure]

/-- Validated inputs are sufficient for total correctness of the public source
entry point; they need not have arrived in canonical representation. -/
theorem gcd_entry_correct (id : Nat) (name : String) (arg : Value) (p g : Poly)
    (hp : Canonical p.terms) (hg : Canonical g.terms)
    (hdata : Polynomials.callPrimitive .gcdInputs arg =
      .ok (.list [value id name p,value id name g]))
    (s : State) (globals : GCDGlobals s)
    (hd : s.env.lookup "m2GCDInputs" = some (.algebra (.builtin .gcdInputs)))
    (budget : Nat)
    (hb : 64 * (max (rank p) (rank g)+1) + 8*rank g + 203 ≤ budget) :
    ∃ out after, Canonical out.terms ∧ MonicOrZero out ∧
      TotalCorrectness.IsGCD Divides p g out ∧ Extends s after ∧
      call budget (.algebra (.library "gcd")) arg s = .ok (value id name out,after) := by
  obtain ⟨next, he, step⟩ := gcd_entry_step (budget-20) arg
    (value id name p) (value id name g) s hdata hd globals.loop
  have hb' : 64 * (max (rank p) (rank g)+1) + 8*rank g + 200 ≤ budget-20+17 := by omega
  obtain ⟨out,after,ho,hm,hgcd,hea,run⟩ := gcd_loop_total id name (max (rank p) (rank g))
    (rank g) p g rfl hp hg (Nat.le_max_left ..) (Nat.le_max_right ..) next
    (globals.of_extends he) (budget-20+17) hb'
  refine ⟨out,after,ho,hm,hgcd,he.trans hea,?_⟩
  have h20 : budget-20+20 = budget := by omega
  simpa only [h20] using step _ _ run

end Macaulean.M2.GCD.Execution
