import Macaulean.Interpreter.Run
import MacauleanTest.NativePolynomialOracle

/-! Compare finite-field basis coefficients and remainders against native M2.
The native observation lifts each coefficient to ZZ and reduces it to a canonical
residue; neither printer spelling nor a native GroebnerBasis tag is compared. -/
namespace Macaulean.M2.FiniteFieldsM2
open Lean Elab Command

def observe (p : Finite.Raw) : Value :=
  .list (p.map fun (c,ns) => .list [Finite.natList ns,.zz c])

private def sameMultiset : List Value → List Value → Bool
  | [], ys => ys.isEmpty
  | x::xs, ys => ys.contains x && sameMultiset xs (ys.erase x)

run_cmd do
  let cases : List (Nat × String) := [
    (2,"x^2-y,x*y-1"), (3,"x^2-y,x*y-1"),
    (5,"x^2-y,x*y-1"), (7,"x^2-y,x*y-1"),
    (5,"2*x^2+3*y,4*x*y+1"), (7,"2*x^2+3*y,4*x*y+1"),
    (5,"0*x"), (5,"x,1-x"), (5,"x^2,x*y,y^2")]
  for (p,generators) in cases do
    let setup := s!"kk=GF({p});rr=kk[x,y];finiteInput=ideal({generators});gg=gb finiteInput;"
    let .ok (.algebra (.finite (.basis _ _ gs _))) := run (setup ++ "gg")
      | throwError "finite-field DSL basis failed: {setup}"
    let actual := gs.map observe
    let observation := "(" ++ setup ++
      "apply(flatten entries gens gg,f->apply(listForm f,t->{t#0,(lift(t#1,ZZ))%" ++ toString p ++ "})))"
    match ← NativePolynomialOracle.query observation with
    | .ok (.ok (.list expected)) =>
      unless sameMultiset actual expected do
        throwError "finite-field native basis mismatch for {setup}\nDSL {repr actual}\nnative {repr expected}"
    | .error error => throwError "finite-field native protocol failed: {error}"
    | .ok .error => throwError "finite-field native source failed: {observation}"
    | .ok (.ok value) => throwError "finite-field native basis has unexpected observation: {repr value}"
    let .ok (.algebra (.finite (.poly _ rem))) := run (setup ++ "(x^3+y^2+2*x+1)%gg")
      | throwError "finite-field DSL remainder failed: {setup}"
    let remObservation := "(" ++ setup ++
      "apply(listForm((x^3+y^2+2*x+1)%gg),t->{t#0,(lift(t#1,ZZ))%" ++ toString p ++ "}))"
    match ← NativePolynomialOracle.query remObservation with
    | .ok (.ok expected) =>
      unless observe rem == expected do
        throwError "finite-field native remainder mismatch for {setup}\nDSL {repr (observe rem)}\nnative {repr expected}"
    | .error error => throwError "finite-field native protocol failed: {error}"
    | .ok .error => throwError "finite-field native source failed: {remObservation}"
  logInfo "FINITE_FIELD_NATIVE_COMPLETE: 9 bases and 9 remainders over F2, F3, F5, F7"

end Macaulean.M2.FiniteFieldsM2
