import MacauleanTest.PolynomialCases
import Macaulean.Interpreter.Check

/-! Native M2 supplies typed coefficient/exponent data; its polynomial printer and
foreign ring identities are not used to decode our polynomials. -/
namespace Macaulean.M2.PolynomialNativeTests
open PolynomialCases Lean Elab Command

private def checkValue (source : String) (expected : Value) : CommandElabM Unit := do
  match ← queryM2 ("(" ++ source ++ ")") with
  | .ok (.ok actual) =>
    unless actual == expected do logError m!"native mismatch: {source}\nexpected {repr expected}\nactual {repr actual}"
  | .ok .error => logError m!"native M2 unexpectedly failed: {source}"
  | .error message => logError m!"native protocol failure for {source}: {message}"

run_cmd do
  for (source, expected) in successes do
    unless run source == .ok expected do
      logError m!"DSL mismatch before native check: {source}\n{repr (run source)}"
    checkValue source expected
  logInfo m!"POLYNOMIAL_TYPED_CASES_COMPLETE: {successes.length}"

-- Explicit mathematical grid: coefficients are written independently of the algebra.
run_cmd do
  let coeffs : List Int := [-2,-1,0,1,2]
  for a in coeffs do
    for b in coeffs do
      let ts : List (Rat × List Nat) :=
        ([(a*a,[2,0]),(2*a*b,[1,1]),(b*b,[0,2])] : List (Int × List Nat)).filterMap
          fun (c,ns) => if c = 0 then none else some ((c : Rat),ns)
      let source := s!"R=QQ[x,y];listForm((({a})*x+({b})*y)^2)"
      let expected := listFormValue ts
      unless run source == .ok expected do logError m!"quadratic grid failed: {source}"
      checkValue source expected
  logInfo "POLYNOMIAL_QUADRATIC_GRID_COMPLETE: 25"

-- Compare the named APIs against independently expressed native operations.
run_cmd do
  let powers : List (Nat × Nat) := [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]
  for (a,b) in powers do
    for (c,d) in powers do
      let m := s!"x^{a}*y^{b}"
      let n := s!"x^{c}*y^{d}"
      let prefix := "R=QQ[x,y];"
      let divides := Value.bool (decide (a ≤ c ∧ b ≤ d))
      let ours := prefix ++ s!"m2MonomialDivides({m},{n})"
      unless run ours == .ok divides do logError m!"divisibility grid failed: {ours}"
      checkValue (prefix ++ s!"(({n})//({m}))*({m})==({n})") divides
      let expected := listFormValue [(1,[max a c,max b d])]
      let ours := prefix ++ s!"listForm(m2MonomialLCM({m},{n}))"
      unless run ours == .ok expected do logError m!"lcm grid failed: {ours}"
      checkValue (prefix ++ s!"listForm(lcm({m},{n}))") expected
      let expectedOrder : Int := if a+b > c+d then 1 else if a+b < c+d then -1
        else if b < d then 1 else if b > d then -1 else 0
      let ours := prefix ++ s!"m2MonomialCompare({m},{n})"
      unless run ours == .ok (.zz expectedOrder) do logError m!"order grid failed: {ours}"
      checkValue (prefix ++ s!"if ({m})==({n}) then 0 else if leadMonomial(({m})+({n}))==({m}) then 1 else -1") (.zz expectedOrder)
      if a ≤ c ∧ b ≤ d then
        let expected := listFormValue [(mkRat 3 2,[c-a,d-b])]
        let ours := prefix ++ s!"listForm(m2MonomialQuotient(3*({n}),2*({m})))"
        unless run ours == .ok expected do logError m!"quotient grid failed: {ours}"
        checkValue (prefix ++ s!"listForm((3*({n}))//(2*({m})))") expected
  logInfo "POLYNOMIAL_MONOMIAL_GRIDS_COMPLETE: 36 pairs, divisibility, lcm, grevlex, and exact quotients"

run_cmd do
  for source in #[
    "R=QQ[x];x/0", "R=QQ[x];leadMonomial(x-x)",
    "R=QQ[x];(x-x)^(-1)", "R=QQ[x];leadTerm(x,x)",
    "R=QQ[x];promote(x)", "QQ=7", "QQ[true]"
  ] do
    match ← queryM2 ("(" ++ source ++ ")") with
    | .ok .error => pure ()
    | .ok (.ok value) => logError m!"native M2 accepted {source}: {repr value}"
    | .error message => logError m!"native error transport failed: {message}"
  logInfo "POLYNOMIAL_NATIVE_ERRORS_COMPLETE: 7"

-- Native classes requiring other extensions must not be silently coerced.
run_cmd do
  let server ← globalM2Server
  for (source, cls) in #[
    ("QQ[x,x]", "PolynomialRing"),
    ("R=QQ[x];(x^2)/x", "frac R"),
    ("R=QQ[x];degree(0*x)", "InfiniteNumber")
  ] do
    let reply : List String ← server.sendRequest "evalValue" ["(" ++ source ++ ")"]
    match reply with
    | ["ok", actual, _] => unless actual == cls do logError m!"unexpected native class for {source}: {actual}"
    | _ => logError m!"native-valid boundary failed for {source}: {repr reply}"
    match run source with
    | .ok value => logError m!"unsupported native boundary silently accepted: {source}: {repr value}"
    | _ => pure ()
  logInfo "POLYNOMIAL_NATIVE_BOUNDARIES_COMPLETE: 3"

run_cmd do
  let source := "R=QQ[x,y];listForm((x-y)*(x+y))"
  let expected := listFormValue [(1,[2,0]),(-1,[0,2])]
  checkValue source expected
  addRunTheorem `Macaulean.M2.PolynomialNativeTests.nativePolynomialCertificate source (.ok expected)
    "Native-M2 agreement followed by a kernel-checked source evaluation."
end Macaulean.M2.PolynomialNativeTests
