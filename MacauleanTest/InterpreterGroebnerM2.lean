import MacauleanTest.PolynomialCases
import MacauleanTest.GroebnerCases
import MacauleanTest.GroebnerChecks
import Macaulean.Interpreter.Check

namespace Macaulean.M2.GroebnerM2Tests
open Lean Elab Command
deriving instance Repr for M2Reply
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

run_cmd do
  let mut failures := 0
  for (source,expected) in PolynomialCases.successes do
    let ours := run source
    unless ours == .ok expected do
      failures := failures + 1
      logError m!"polynomial result mismatch {repr source}: {repr ours} versus {repr expected}"
    let native ← queryM2 source
    unless native == .ok (.ok expected) do
      failures := failures + 1
      logError m!"native polynomial result mismatch {repr source}: {repr native} versus {repr expected}"
  unless failures == 0 do throwError "{failures} polynomial value comparisons failed"
  logInfo m!"POLYNOMIAL_TYPED_RESULTS_COMPLETE: {PolynomialCases.successes.length} exact observations"

run_cmd do
  let mut failures := 0
  for source in PolynomialCases.errors do
    match run source with
    | .error _ => pure ()
    | result =>
      failures := failures + 1
      logError m!"expected runtime error, got {repr result} for {repr source}"
    unless (← queryM2 source) == .ok .error do
      failures := failures + 1
      logError m!"native M2 did not raise the expected runtime error: {repr source}"
  for source in PolynomialCases.unsupported do
    match run source with
    | .error _ => pure ()
    | result =>
      failures := failures + 1
      logError m!"unsupported algebra was silently accepted: {repr source}, {repr result}"
  for source in PolynomialCases.invalidSyntax do
    if (parse source).isOk then
      failures := failures + 1
      logError m!"accepted malformed syntax: {repr source}"
  unless failures == 0 do throwError "{failures} polynomial rejection controls failed"
  logInfo m!"POLYNOMIAL_REJECTIONS_COMPLETE: {PolynomialCases.errors.length} native errors, {PolynomialCases.unsupported.length} explicit scope rejections, {PolynomialCases.invalidSyntax.length} parser errors"

/-- Compare monic reduced bases, not display strings or generator order. -/
def nativeObservation (c : GroebnerCases.Case) : String :=
  "(" ++ c.setup ++
  "observe:=(xs,j)->if j==#xs then {} else if xs#j==0 then observe(xs,j+1) else " ++
  "{listForm ((xs#j)/(leadCoefficient (xs#j)))}|observe(xs,j+1);" ++
  "observe(flatten entries gens gb ii,0))"

run_cmd do
  let mut count := 0
  let mut maximumCells := 0
  for c in GroebnerCases.systems do
    let .ok t := parse c.source | throwError "failed to parse case {c.name}"
    let start ← IO.monoMsNow
    let result := Runtime.evaluate t
    let elapsed := (← IO.monoMsNow) - start
    let .ok result := result | throwError "gb failed in {c.name}: {repr result}"
    let .basis g := result.value | throwError "gb did not return a basis in {c.name}"
    match GroebnerChecks.check g with
    | .ok _ => pure ()
    | .error error => throwError "basis verification failed in {c.name}: {error}"
    let .list ours := GroebnerChecks.observed g | throwError "invalid local basis observation"
    let .ok (.ok (.list native)) ← queryM2 (nativeObservation c)
      | throwError "native GB oracle failed in {c.name}"
    unless GroebnerChecks.sameMultiset ours native do
      throwError "different reduced bases in {c.name}: ours={repr ours}; native={repr native}"
    maximumCells := max maximumCells result.state.heap.cells.length
    count := count + 1
    logInfo m!"GB_CASE {c.name}: {g.generators.length} generators, {elapsed} ms, {result.state.heap.cells.length} lexical cells"
  unless count == GroebnerCases.systems.length do throwError "incomplete GB corpus"
  logInfo m!"GROEBNER_NATIVE_COMPLETE: {count} systems, ideal/provenance/S-pair/reducedness checks; max cells={maximumCells}"
end Macaulean.M2.GroebnerM2Tests
