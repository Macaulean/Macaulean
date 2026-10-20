import Macaulean.Verification.NatContracts.Command

/-!
# Verified M2 functions over natural numbers

`import Macaulean.Verification.NatContracts` and `open M2`, define an M2 function in
the worksheet, then state its contract with `#m2_verify`. Verification conditions
are generated from the function's compiled code (`NatContracts.Wp`) and are sound
for the production runtime by a single theorem (`NatContracts.Soundness`).
-/
