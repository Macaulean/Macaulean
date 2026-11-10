import Macaulean.Interpreter.Groebner
import Macaulean.Interpreter.Check
import MacauleanTest.GroebnerChecks

/-! Kernel examples, adversarial checks, and snapshot replay for actual library
execution. No native_decide, added axioms, or proof holes. -/
namespace Macaulean.M2.GroebnerTests
open Lean Elab Command
set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

example : run "R=QQ[x];numgens gb ideal(0*x)" = .ok (.zz 0) := by decide +kernel
example : run "R=QQ[x];listForm(normalForm(x^2+1,{x-1}))" =
    .ok (.list [.sequence [.list [.zz 0],.qq 2]]) := by decide +kernel
example : run "R=QQ[x];listForm(sPolynomial(x^2-1,x-1))" =
    .ok (.list [.sequence [.list [.zz 1],.qq 1],.sequence [.list [.zz 0],.qq (-1)]]) := by decide +kernel
example : runWithFuel 2 "R=QQ[x];gb ideal(x^2-1)" = .error .fuelExhausted := by decide +kernel
example : (Value.ofWire ["GroebnerBasis","0"]).isOk = false := by decide +kernel
example : (Value.ofWire ["Matrix","0","1"]).isOk = false := by decide +kernel

-- A full basis and its exact coefficient row are reified into a kernel-checked
-- theorem. The expected object is written explicitly, not inferred from output.
run_cmd do
  let r : Polynomials.RingInfo := ⟨0,["x"]⟩
  let expected := Outcome.ok (.algebra (.basis r [[(2,[1])]] [[(1,[1])]] [[[(mkRat 1 2,[0])]]]))
  let source := "R=QQ[x];gb ideal(2*x)"
  unless run source == expected do throwError "principal basis/certificate data is wrong"
  addRunTheorem `Macaulean.M2.GroebnerTests.principalBasisCertificate source expected
    "Kernel-checked execution of the M2 Buchberger library, including exact provenance."
  let source := "R=QQ[x];I=ideal(2*x);G=gb I;gens I*getChangeMatrix G==gens G"
  addRunTheorem `Macaulean.M2.GroebnerTests.changeMatrixCertificate source (.ok (.bool true))
    "Kernel-checked source-language basis change identity."
  logInfo "BUCHBERGER_KERNEL_CERTIFICATES_COMPLETE: basis object and change-matrix identity"

-- Independent oracle mutation controls: each defect must actually be detected.
run_cmd do
  let r : Polynomials.RingInfo := ⟨0,["x","y"]⟩
  let x : GroebnerChecks.Poly := [(1,[1,0])]
  let y : GroebnerChecks.Poly := [(1,[0,1])]
  let one : GroebnerChecks.Poly := [(1,[0,0])]
  let p : GroebnerChecks.Poly := [(1,[2,0]),(-1,[0,1])]
  let q : GroebnerChecks.Poly := [(1,[1,1]),(-1,[0,0])]
  let good := Polynomials.Object.basis r [x,y] [x,y] [[one,[]],[[],one]]
  unless (GroebnerChecks.check good).isOk do throwError "independent checker rejected a correct basis"
  let controls : List (String × Polynomials.Object) := [
    ("wrong provenance", .basis r [x,y] [x,y] [[[],[]],[[],one]]),
    ("missing generator", .basis r [x,y] [x] [[one,[]]]),
    ("incomplete S-pairs", .basis r [p,q] [p,q] [[one,[]],[[],one]]),
    ("reducible tail", .basis r [x++y,y] [x++y,y] [[one,[]],[[],one]]),
    ("nonmonic", .basis r [[(2,[1,0])]] [[(2,[1,0])]] [[one]]),
    ("zero output", .basis r [x] [[]] [[[]]]),
    ("wrong exponent dimension", .basis r [[(1,[1])]] [[(1,[1])]] [[one]]),
    ("noncanonical terms", .basis r [x] [x++x] [[one]]),
    ("wrong row count", .basis r [x,y] [x,y] [[one,[]]]),
    ("wrong row width", .basis r [x,y] [x,y] [[one],[[],one]]),
    ("duplicate leading monomial", .basis r [x,x] [x,x] [[one,[]],[[],one]])]
  for (label,bad) in controls do
    if (GroebnerChecks.check bad).isOk then throwError "checker accepted {label}"
  if (GroebnerChecks.normalForm 0 [] []).isOk then throwError "checker treats exhaustion as success"
  unless GroebnerChecks.sameMultiset [.zz 1,.zz 2] [.zz 2,.zz 1] do throwError "multiset checker rejected permutation"
  if GroebnerChecks.sameMultiset [.zz 1,.zz 1] [.zz 1,.zz 2] then throwError "multiset checker ignored multiplicity"
  logInfo "BUCHBERGER_ORACLE_NEGATIVE_CONTROLS_COMPLETE: 11 malformed bases and reduction exhaustion"

-- These are precise interpreter errors, not generic native error/error matches.
run_cmd do
  let errors : List (String × Error) := [
    ("gb()", .algebra "ideal construction requires a polynomial to determine the ring"),
    ("gb 7", .algebra "ideal construction requires a polynomial to determine the ring"),
    ("R=QQ[x];normalForm(x,x,x)", .arity 2 3),
    ("R=QQ[x];sPolynomial(0*x,x)", .algebra "zero polynomial has no leading monomial"),
    ("R=QQ[x];normalForm(x,{true})", .algebra "cannot promote Boolean to QQ[x]"),
    ("normalForm(0,{})", .algebra "normal form requires a polynomial ring"),
    ("R=QQ[x];G=gb ideal(0*x);S=QQ[x];normalForm(0*x,G)", .algebra "polynomials belong to different rings"),
    ("R=QQ[x];p=x;S=QQ[x];normalForm(p,{x})", .algebra "polynomials belong to different rings"),
    ("R=QQ[x];I=ideal(x);m2MakeBasis(I,{{x,{0}}})", .algebra "invalid basis provenance"),
    ("R=QQ[x];I=ideal(x);m2MakeBasis(I,{{x,{1,0}}})", .algebra "coefficient row has the wrong dimension"),
    ("R=QQ[x];I=ideal(x);m2MakeBasis(I,{{0*x,{0}}})", .algebra "basis contains a zero polynomial"),
    ("R=QQ[x];I=ideal(x);m2MakeBasis(I,{{2*x,{2}}})", .algebra "basis must be monic"),
    ("R=QQ[x];getChangeMatrix ideal(x)", .algebra "expected a Groebner basis"),
    ("gb=1", .protectedSymbol "gb"),
    ("m2gbLoop=1", .protectedSymbol "m2gbLoop"),
    ("R=QQ[x];numRows(gens ideal(x,x)*gens ideal(x))", .algebra "matrix multiplication dimension mismatch")]
  for (source,expected) in errors do
    let actual := run source
    unless actual == .error expected do throwError "wrong error for {source}: {repr actual}"
  let r : Polynomials.RingInfo := ⟨0,["x"]⟩
  let malformed := Value.algebra (.matrix r 2 [[[(1,[1])]]])
  let .error (.algebra "invalid matrix dimensions") := Polynomials.asMatrix malformed
    | throwError "malformed matrix dimensions were truncated or misclassified"
  logInfo m!"BUCHBERGER_ERROR_CONTROLS_COMPLETE: {errors.length} source cases and malformed matrix data"

private def execute (s : Session) (source : String) (fuel := Runtime.defaultFuel) : Except String Session.Result := do
  let term ← parse source
  return s.step term false fuel

run_cmd do
  let .ok initial := execute {} "R=QQ[x,y];p=x;I=ideal(x^2-y,x*y-1);G=gb I"
    | throwError "snapshot setup did not parse"
  let .ok _ := initial.outcome | throwError "snapshot setup failed"
  let original := initial.session
  let .ok changed := execute original "S=QQ[x,y];gb ideal(x,y)"
    | throwError "snapshot edit did not parse"
  let .ok _ := changed.outcome | throwError "snapshot edit failed"
  unless changed.session.heap.nextRing == original.heap.nextRing+1 do
    throwError "successful edit did not allocate a new ring"
  for source in ["G=gb I;1/0", "S=QQ[x,y];G=gb ideal(x,y);1/0"] do
    let .ok failed := execute original source | throwError "rollback test did not parse"
    unless failed.outcome == .error .divByZero do throwError "missing rollback error"
    unless failed.session.env == original.env && failed.session.heap.cells == original.heap.cells &&
        failed.session.heap.nextRing == original.heap.nextRing && failed.session.scope == original.scope &&
        failed.session.fileFrame == original.fileFrame && failed.output.isNone do
      throwError "failed Buchberger input published a partial result or changed state"
  let .ok exhausted := execute original "G=gb I" 12 | throwError "depth test did not parse"
  unless exhausted.outcome == .error .fuelExhausted && exhausted.session.env == original.env &&
      exhausted.session.heap.cells == original.heap.cells && exhausted.output.isNone do
    throwError "depth exhaustion published a basis or leaked allocation"
  for s in [original,changed.session,exhausted.session] do
    let .ok replay := execute s "(p^3-1)%G" | throwError "replay did not parse"
    let .ok (.algebra (.poly r terms)) := replay.outcome | throwError "snapshot replay failed"
    unless terms.isEmpty && r.id == 0 do throwError "old basis or ring changed in a later snapshot"
  -- Callers' lexical locals must not replace the protected algorithm's helpers.
  let .ok shadow := execute original "f=()->(m2gbLoop:=7;gb I);gens(f())==gens G"
    | throwError "shadow test did not parse"
  unless shadow.outcome == .ok (.bool true) do throwError "caller scope captured a library helper"
  logInfo "BUCHBERGER_SNAPSHOTS_COMPLETE: edit replay, failure rollback, depth exhaustion and caller-scope isolation"
end Macaulean.M2.GroebnerTests
