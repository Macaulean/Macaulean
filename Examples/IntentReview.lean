import Macaulean.Verification

/-!
# Review an M2 function's intended behavior

Open this file in Lean. Ordinary M2 appears below. Select the last command to see
its deterministic contract card. Inspect its domain and exclusions before using
"Record approval in source". No approval is prefilled, and this example does not
claim that any function has been proved correct.

Intent review is snapshot-specific: finish the M2 setup before approving a target.
A later runtime change conservatively invalidates that approval in stage 1.
-/
open M2

samePolynomial = p -> p;
remainderBy = (p, G) -> normalForm(p, G);

R = QQ[x,y];
f = x^2 + 2*x*y + y^2;

samePolynomial f
-- Ordinary M2 output; this is not a universal correctness theorem.

remainderBy(f, {x-y})
-- Ordinary ordered division; no canonical choice is promised for arbitrary G.

#m2_contract "samePolynomial" polynomialIdentity
#m2_contract "remainderBy" orderedRemainder

-- Review the card on either command above. The panel can insert the exact
-- #m2_approve directive, #m2_revoke, or #print for the named Lean proposition.
-- Proof status remains "unattempted" throughout this stage.
