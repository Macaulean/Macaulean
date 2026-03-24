/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.Algebra.Instances
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Simp

/-!
# Algebra solver extension for `grind`

Registers a solver extension slot for algebra-aware reasoning. Currently, the
`@[grind =]` lemmas in `Defs.lean` handle all algebraMap homomorphism properties
via E-matching, which integrates tightly with the ring solver's normalization.

The extension provides a hook point for future enhancements that require active
participation beyond what E-matching can do:

- **Subalgebra lifting**: Detecting when a ring solver polynomial has all
  variables in `im(algebraMap)` and lifting the entire computation to `R`.
- **Cross-ring Gröbner**: Using `R`'s Gröbner basis results to prune `A`'s search.
- **Certificate verification**: Efficiently checking M2-provided factorization
  certificates by verifying coefficient arithmetic in `R`.

These require the `mbtc` (model-based theory combination) or `action` hooks,
not just `internalize`/`newEq`.
-/

open Lean Meta Grind

namespace Lean.Meta.Grind.Algebra

/-- State for the algebra solver extension. -/
structure ExtState where
  deriving Inhabited

end Lean.Meta.Grind.Algebra

/-- The algebra solver extension registration. -/
initialize algebraExt : SolverExtension Lean.Meta.Grind.Algebra.ExtState ←
  registerSolverExtension (return {})

namespace Lean.Meta.Grind.Algebra

/-- Internalize handler. -/
def internalize (_e : Expr) (_parent? : Option Expr) : GoalM Unit := do
  return ()

/-- Equality handler. -/
def processNewEq (_lhs _rhs : Expr) : GoalM Unit := do
  return ()

end Lean.Meta.Grind.Algebra

initialize
  algebraExt.setMethods
    (internalize := Lean.Meta.Grind.Algebra.internalize)
    (newEq := Lean.Meta.Grind.Algebra.processNewEq)
