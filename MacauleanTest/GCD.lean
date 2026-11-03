import MacauleanTest.GCDCases
import Macaulean.Interpreter.GCD.TotalCorrectness
import Macaulean.Interpreter.GCD.Normalization
import Macaulean.Interpreter.GCD.Execution
import Macaulean.Interpreter.GCD.Reduction
import Macaulean.Interpreter.GCD.ReductionCorrectness
import Macaulean.Interpreter.GCD.NormalForm
import Macaulean.Interpreter.GCD.ComputeCorrectness
import Macaulean.Interpreter.GCD.AutomaticCorrectness
import Macaulean.Interpreter.DSL

namespace Macaulean.M2.GCDTests
open Lean Elab Command
set_option maxRecDepth 50000
set_option maxHeartbeats 30000000

-- Concrete kernel execution of the degree-budget API, including the all-zero
-- and constant cases. These are execution theorems, not universal GCD proofs.
example : GCD.compute (poly [(1,[4]),(-1,[0])]) (poly [(1,[3]),(-1,[0])]) =
    .ok (poly [(1,[1]),(-1,[0])]) := by decide +kernel

example : GCD.compute (poly []) (poly []) = .ok (poly []) := by decide +kernel

example : GCD.compute (poly [(2,[0])]) (poly [(-3,[0])]) =
    .ok (poly [(1,[0])]) := by decide +kernel

example : (Library.sourceFor "gcd").map Prod.fst =
    some "Macaulean/Interpreter/GCD.m2" := by decide +kernel
example : (Library.sourceFor "normalForm").map Prod.fst =
    some "Macaulean/Interpreter/Buchberger.m2" := by decide +kernel
example : Library.sourceFor "notALibraryFunction" = none := by decide +kernel

-- Raw inputs are normalized before the degree is used; cancelling large terms
-- must not corrupt the answer or force an inflated bound.
example : Polynomials.gcdInputs (.sequence [
    poly [(1,[1000]),(-1,[1000]),(2,[1]),(2,[0])], poly []]) =
    .ok (⟨0,["x"]⟩, [(2,[1]),(2,[0])], []) := by decide +kernel

example : GCD.compute (poly [(1,[1,0])]) (poly []) =
    .error (.algebra "polynomial exponent vector has the wrong dimension") := by decide +kernel

run_cmd do
  for name in [``GCD.TotalCorrectness.loop_total,
      ``GCD.TotalCorrectness.input_bound_total, ``GCD.TotalCorrectness.degree_bound_total,
      ``GCD.Univariate.normalize_canonical, ``GCD.Univariate.normalize_below,
      ``GCD.Univariate.canonical_ext, ``GCD.Univariate.normalize_idempotent,
      ``GCD.Univariate.cancellation_decreases, ``GCD.Univariate.cancellation_rank_lt,
      ``GCD.Univariate.sub_head, ``GCD.Univariate.sub_head_rank_lt,
      ``GCD.Univariate.eval_sub, ``GCD.Univariate.eval_mul,
      ``GCD.Univariate.leading_coefficient, ``GCD.Univariate.leading_monomial,
      ``GCD.Univariate.monomial_quotient, ``GCD.Univariate.eval_cancellation,
      ``GCD.Univariate.mul_assoc, ``GCD.Univariate.mul_comm,
      ``GCD.Univariate.mul_add, ``GCD.Univariate.mul_sub,
      ``GCD.Univariate.common_divisors_sub, ``GCD.Univariate.scale_eq_mul,
      ``GCD.Univariate.monicNormalize_monic, ``GCD.Univariate.monicNormalize_divides,
      ``GCD.Univariate.divides_monicNormalize, ``GCD.Univariate.eval_div_scalar,
      ``GCD.Univariate.eval_eq_zero, ``GCD.Univariate.monomial_divides,
      ``GCD.Execution.gcd_both_zero, ``GCD.Execution.gcd_second_zero,
      ``GCD.Execution.gcd_step,
      ``GCD.Execution.reducer_end, ``GCD.Execution.reducer_divides,
      ``GCD.Execution.reducer_not_divides, ``GCD.Execution.subtract_row_empty,
      ``GCD.Execution.Extends.read_ref, ``GCD.Execution.Extends.write_private,
      ``GCD.Execution.InFrame.read, ``GCD.Execution.InFrame.write_result,
      ``GCD.Univariate.leading_term, ``GCD.Univariate.eval_add,
      ``GCD.Univariate.eval_mul_scalar, ``GCD.Univariate.eval_mul_scalar_monomial,
      ``GCD.Execution.reduction_zero, ``GCD.Execution.reduction_move_head,
      ``GCD.Execution.reduction_coefficient, ``GCD.Execution.reduction_cancel_recurse,
      ``GCD.Execution.reduction_cancel, ``GCD.Execution.reduction_dispatch,
      ``GCD.Execution.cancellation_step, ``GCD.Execution.move_head_step,
      ``GCD.Execution.reduction_total, ``GCD.Execution.ReductionTrace.degree_bound,
      ``GCD.Execution.ReductionTrace.common_divisors,
      ``GCD.Execution.reduction_correct,
      ``GCD.Univariate.promote_self, ``GCD.Univariate.normal_form_data,
      ``GCD.Univariate.zero_mul_polynomial,
      ``GCD.Execution.bare_pairs_end, ``GCD.Execution.bare_pairs_singleton,
      ``GCD.Execution.normal_form_correct, ``GCD.Execution.gcd_loop_total,
      ``GCD.Execution.gcd_entry_correct, ``GCD.Execution.input_fuel_sufficient,
      ``GCD.Execution.compute_correct_canonical, ``GCD.Execution.compute_correct_validated,
      ``GCD.Execution.validated_has_canonical, ``GCD.Execution.compute_total,
      ``GCD.Execution.automatic_call_eq, ``GCD.Execution.automatic_call_correct] do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"

run_cmd do
  for (f,g,d) in cases do
    let input := "R=QQ[x];{" ++ s!"{f},{g},{d}" ++ "}"
    let .ok (.list [fv,gv,expected]) := run input
      | throwError "invalid GCD test input: {input}"
    unless GCD.compute fv gv == .ok expected do
      throwError "input-derived GCD budget/answer failed: {input}\n{repr (GCD.compute fv gv)}"
    let source := s!"R=QQ[x];gcd({f},{g})==({d})"
    unless run source == .ok (.bool true) do
      throwError "source GCD failed: {source}\n{repr (run source)}"
  -- Long division with many cancellations, and a Euclidean chain dropping one
  -- degree per iteration. These exercise different contributions to depth.
  for d in [8,16,32,64] do
    let f := poly [(1,[d]),(-1,[0])]
    let g := poly [(1,[1]),(-1,[0])]
    unless GCD.compute f g == .ok g do
      throwError "long-division degree-budget regression at degree {d}"
  -- The input-derived API must work beyond the worksheet's fixed default.
  let large := poly [(1,[1024]),(-1,[0])]
  let linear := poly [(1,[1]),(-1,[0])]
  unless GCD.compute large linear == .ok linear do
    throwError "input-derived budget failed beyond the default depth"
  match Runtime.finish (Runtime.call Runtime.defaultFuel (.algebra (.library "gcd"))
      (.sequence [large,linear]) {}) with
  | .error .fuelExhausted => pure ()
  | other => throwError "fixed-depth control returned an unexpected outcome: {repr other}"
  let mut previous : Polynomials.Raw := [(1,[0])]
  let mut current : Polynomials.Raw := [(1,[1])]
  for i in List.range 32 do
    let .ok product := Polynomials.mul 1 [(1,[1])] current
      | throwError "failed to construct Euclidean-chain input"
    let .ok next := Polynomials.add 1 product previous
      | throwError "failed to construct Euclidean-chain input"
    previous := current
    current := next
    if (i+2) % 8 == 0 then
      unless GCD.compute (poly current) (poly previous) == .ok (poly [(1,[0])]) do
        throwError "Euclidean-chain degree-budget regression at degree {i+2}"
  for source in [
    "R=QQ[x];applyGCD=(h,f,g)->h(f,g);applyGCD(gcd,x^4-1,x^3-1)==x-1",
    "R=QQ[x];f=(normalForm)->gcd(x^4-1,x^3-1);f(17)==x-1",
    "R=QQ[x];ring gcd(0*x,0*x)===R"
  ] do
    unless run source == .ok (.bool true) do
      throwError "GCD function/ring contract failed: {source}\n{repr (run source)}"
  for (source,expected) in [
    ("gcd(12,8)", Error.algebra "expected a polynomial, got ZZ"),
    ("R=QQ[x];gcd(x)", Error.arity 2 1),
    ("R=QQ[x];gcd(x,x,x)", Error.arity 2 3),
    ("R=QQ[x,y];gcd(x,y)", Error.algebra "gcd requires a univariate polynomial ring over QQ"),
    ("R=QQ[];gcd(promote(1,R),promote(0,R))",
      Error.algebra "gcd requires a univariate polynomial ring over QQ"),
    ("R=QQ[x];p=x;S=QQ[y];gcd(p,y)",
      Error.algebra "gcd polynomials belong to different rings"),
    ("gcd=17", Error.protectedSymbol "gcd")
  ] do
    unless run source == .error expected do
      throwError "GCD rejection contract failed: {source}\n{repr (run source)}"
  unless runWithFuel 1 "R=QQ[x];gcd(x,x)" == .error .fuelExhausted do
    throwError "explicit worksheet fuel must remain effective"
  logInfo m!"GCD_CASES_COMPLETE: {cases.length} answers, input-derived budgets, boundaries"

-- Actual scoped worksheet syntax.
run_cmd do
  for source in [
      "R=QQ[x];gcd(x^1024-1,x-1)==x-1",
      "R=QQ[x];h=gcd;h(x^1024-1,x-1)==x-1",
      "R=QQ[x];applyGCD=(h,f,g)->h(f,g);applyGCD(gcd,x^1024-1,x-1)==x-1",
      "R=QQ[x];outer=(f,g)->(keep:=37;d:=gcd(f,g);{d,keep});outer(x^1024-1,x-1)=={x-1,37}"
    ] do
    let .ok term := parse source | throwError "invalid automatic GCD test"
    let result := ({} : Session).step term (fuel := 64)
    unless result.outcome == .ok (.bool true) do
      throwError "automatic worksheet GCD failed: {source}\n{repr result.outcome}"
  let .ok invalid := parse "R=QQ[x,y];gcd(x,y)" | throwError "invalid rejection test"
  unless (({} : Session).step invalid (fuel := 64)).outcome ==
      .error (.algebra "gcd requires a univariate polynomial ring over QQ") do
    throwError "automatic GCD must preserve validation errors"

open _root_.M2
#guard_msgs in
R = QQ[x];
/-- info: o2 = x - 1 : QQ[x] -/
#guard_msgs in
gcd(x^4-1,x^3-1)

/-- info: o3 = x - 1 : QQ[x] -/
#guard_msgs in
set_option m2.maxDepth 64 in
gcd(x^1024-1,x-1)

/-- info: o4 = true : Boolean -/
#guard_msgs in
set_option m2.maxDepth 64 in
(h = gcd; outer = (fn,f,g) -> (keep := 37; d := fn(f,g); {d,keep});
 outer(h,x^1024-1,x-1) == {x-1,37})

end Macaulean.M2.GCDTests
