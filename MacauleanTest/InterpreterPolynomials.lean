import MacauleanTest.PolynomialCases
import Macaulean.Interpreter.Session
import Macaulean.Interpreter.Check

/-! Kernel evaluation of the source runtime, not an alternate algebra evaluator. -/
namespace Macaulean.M2.PolynomialTests
open PolynomialCases Lean Elab Command
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000

-- Diagnostics identify every failed case; the following examples are kernel proofs.
run_cmd do
  for (src, expected) in successes ++ helpers do
    unless run src == .ok expected do
      logError m!"polynomial case failed: {src}\nexpected {repr expected}\nreceived {repr (run src)}"
  for (src, expected) in errors do
    unless run src == .error expected do
      logError m!"polynomial error contract failed: {src}\nexpected {repr expected}\nreceived {repr (run src)}"
example : (successes ++ helpers).all (fun (src,v) => run src == .ok v) = true := by decide +kernel
example : errors.all (fun (src,e) => run src == .error e) = true := by decide +kernel

private def rejected (s : String) : Bool :=
  match run s with | .ok _ => false | _ => true
example : unsupported.all rejected = true := by decide +kernel

example : parse "QQ[x,y]" = .ok (.polyRing (.var "QQ") ["x","y"]) := by decide +kernel
example : parse "QQ[]" = .ok (.polyRing (.var "QQ") []) := by decide +kernel
example : parse "gens QQ[x,y]" = .ok (.apply (.var "gens") (.polyRing (.var "QQ") ["x","y"])) := by decide +kernel
example : parse "f=()->QQ[x]" = .ok (.assign "f" (.lambda (.fixed []) (.polyRing (.var "QQ") ["x"]))) := by decide +kernel
example : parse "QQ[x,\n y]" = parse "QQ[x,y]" := by decide +kernel

private def malformed : List String := [
  "QQ[", "QQ[x", "QQ[x}", "QQ[x)]", "QQ[x,,y]", "QQ[,x]",
  "QQ[x,]", "QQ[x+y]", "QQ[(x)]", "QQ[1]", "QQ[{x}]", "QQ[x;y]",
  "QQ[x y]", "[x,y]", "QQ[x] ]", "QQ[if]"
]
example : malformed.all (fun s => (parse s).isError) = true := by decide +kernel

-- Checked conversion rejects malformed exponent dimensions before invoking algebra.
example : (Polynomials.decode 2 [(1,[1])]).isError = true := by decide +kernel
example : (Polynomials.normalized 2 [(1,[1,0]),(2,[0])]).isError = true := by decide +kernel
example : Polynomials.normalized 2 [(2,[0,1]),(1,[1,0]),(-2,[0,1]),(0,[9,9])] =
    .ok [(1,[1,0])] := by decide +kernel
example : Polynomials.divides [1] [1,2] = false := by decide +kernel
example : Polynomials.divides [1,2] [1] = false := by decide +kernel
example : runWithFuel 1 "QQ[x]" = .error .fuelExhausted := by decide +kernel

private def execute (s : Session) (src : String) : Session.Result :=
  match parse src with
  | .ok term => s.step term
  | .error _ => ⟨s, .error .invalidReference, none, []⟩
private def initial : Session := (execute {} "R=QQ[x,y];p=x+y").session
private def changed : Session := (execute initial "p=p^2").session
example : (execute initial "size p").outcome = .ok (.zz 2) := by decide +kernel
example : (execute changed "size p").outcome = .ok (.zz 3) := by decide +kernel
private def failed : Session := (execute initial "(S=QQ[x];p=17;1/0)").session
example : failed.heap.nextRing = initial.heap.nextRing := by decide +kernel
example : failed.lookup "S" = none := by decide +kernel
example : (execute failed "ring x==R").outcome = .ok (.bool true) := by decide +kernel
example : (execute failed "size p").outcome = .ok (.zz 2) := by decide +kernel
private def skipped : Session := (execute initial "if false then QQ[z]").session
example : skipped.heap.nextRing = initial.heap.nextRing := by decide +kernel
example : skipped.lookup "z" = none := by decide +kernel

-- Algebra handles are not transported across independent runtime sessions.
example : (Value.ofWire ["PolynomialRing","0","x"]).isError = true := by decide +kernel
example : (Value.ofWire ["Polynomial","0","1","1"]).isError = true := by decide +kernel
example : (Value.ofWire ["List","1","PolynomialRing","0","x"]).isError = true := by decide +kernel

-- Actual certificate reification, including the polynomial's ring and rational payload.
run_cmd do
  let src := "R=QQ[x,y];(x+y/2)^2"
  let value := Value.algebra (.poly ⟨0,["x","y"]⟩
    [(1,[2,0]),(1,[1,1]),(mkRat 1 4,[0,2])])
  addRunTheorem `Macaulean.M2.PolynomialTests.polynomialCertificate src (.ok value)
    "Kernel-checked polynomial evaluation, not a theorem that a basis is Groebner."
example : run "R=QQ[x,y];(x+y/2)^2" = .ok (.algebra (.poly ⟨0,["x","y"]⟩
    [(1,[2,0]),(1,[1,1]),(mkRat 1 4,[0,2])])) := polynomialCertificate
end Macaulean.M2.PolynomialTests
