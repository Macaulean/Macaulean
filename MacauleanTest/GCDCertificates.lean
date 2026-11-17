import Macaulean.Verification

namespace Macaulean.M2.GCDCertificateTests
open Lean Elab Command
set_option maxRecDepth 50000
set_option maxHeartbeats 30000000
open _root_.M2

#guard_msgs in
R = QQ[x];
#guard_msgs in
f = x^4-1;
#guard_msgs in
g = x^3-1;
#guard_msgs in
d = gcd(f,g);

/-- info: Macaulean.M2.GCDCertificateTests.resultProof : a kernel-checked monic GCD certificate for the selected worksheet values -/
#guard_msgs in
#m2_gcd_proof resultProof "f" "g" "d"

private def poly (terms : Polynomials.Raw) : Value :=
  .algebra (.poly ⟨0, ["x"]⟩ terms)

-- A named certificate is an ordinary reusable theorem with exact input values.
example : GCD.ValueSpec (poly [(1,[4]),(-1,[0])])
    (poly [(1,[3]),(-1,[0])]) (poly [(1,[1]),(-1,[0])]) := resultProof

/-- error: worksheet result does not equal the monic GCD -/
#guard_msgs in
#m2_gcd_proof wrongProof "f" "g" "f"

/-- error: unknown worksheet binding missing -/
#guard_msgs in
#m2_gcd_proof missingProof "missing" "g" "d"

#guard_msgs in
n = 12;
/-- error: GCD validation/execution failed: expected a polynomial, got ZZ -/
#guard_msgs in
#m2_gcd_proof invalidProof "n" "g" "d"

run_cmd do
  for name in [`Macaulean.M2.GCDCertificateTests.wrongProof,
      `Macaulean.M2.GCDCertificateTests.missingProof,
      `Macaulean.M2.GCDCertificateTests.invalidProof] do
    if (← getEnv).contains name then
      throwError "rejected certificate installed a declaration: {name}"

-- Worksheet mutation cannot change the proposition of an existing theorem.
#guard_msgs in
f = x;
#guard_msgs in
g = x^2;
#guard_msgs in
d = gcd(f,g);
example : GCD.ValueSpec (poly [(1,[4]),(-1,[0])])
    (poly [(1,[3]),(-1,[0])]) (poly [(1,[1]),(-1,[0])]) := resultProof

/-- info: Macaulean.M2.GCDCertificateTests.updatedProof : a kernel-checked monic GCD certificate for the selected worksheet values -/
#guard_msgs in
#m2_gcd_proof updatedProof "f" "g" "d"
example : GCD.ValueSpec (poly [(1,[1])])
    (poly [(1,[2])]) (poly [(1,[1])]) := updatedProof

run_cmd do
  for name in [``GCD.certify_result, ``resultProof, ``updatedProof] do
    for dependency in ← Lean.collectAxioms name do
      unless dependency ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name} depends on unapproved axiom {dependency}"
  logInfo "GCD_CERTIFICATES_COMPLETE: reusable results, rejections, snapshots, axiom audits"

end Macaulean.M2.GCDCertificateTests
