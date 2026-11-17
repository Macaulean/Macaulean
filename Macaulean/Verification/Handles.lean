import Macaulean.Verification.Handles.Tactic

/-!
# Worksheet M2 functions as Lean terms

`import Macaulean.Verification.Handles` and `open M2`. Every M2 function definition
then also defines a Lean constant `M2.<name> : Macaulean.M2.Fn`, and `m2_fn% name`
refers to the function bound to `name` at that point of the worksheet. State and
prove ordinary theorems such as `gcdNat (a, b) ⇓ Nat.gcd a b` or `gcdNat (a, b) ↓`
with `m2_unfold` (one step of the function), `m2_use` (a proved call) and `m2_eval`.
See `docs/m2-verified-functions.md`.
-/
