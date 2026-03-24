/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Macaulean.Grind.AlgPoly.Reify
import Macaulean.Grind.AlgPoly.Denote
import Macaulean.Grind.Algebra.Instances
import Lean.Elab.Tactic.Basic

/-!
# algebra_norm tactic

Verifies polynomial identities in algebras with two-level normalization.

## Strategy

1. Try `grind` first — the @[grind =] lemmas handle many cases including
   hypothesis propagation from the coefficient ring.
2. If grind fails, expand compound algebraMap args via `simp`, then retry `grind`.
   This handles complex polynomial identities where E-matching alone isn't enough.
-/

open Lean Meta Elab Tactic

namespace Macaulean.AlgPoly.Tactic

elab "algebra_norm" : tactic => do
  -- Strategy 1: try grind directly (handles hypotheses, simple identities)
  try
    evalTactic (← `(tactic| grind))
    return
  catch _ => pure ()
  -- Strategy 2: contract algebraMap products/sums + grind
  try
    evalTactic (← `(tactic|
      (simp (config := { maxSteps := 200000 }) only [
        ← Lean.Grind.Algebra.algebraMap_mul, ← Lean.Grind.Algebra.algebraMap_add,
        ← Lean.Grind.Algebra.algebraMap_sub, ← Lean.Grind.Semiring.mul_assoc,
        ← Lean.Grind.Semiring.right_distrib,
        Lean.Grind.Algebra.algebraMap_smul_def];
       grind)))
    return
  catch _ => pure ()
  -- Strategy 3: expand algebraMap via simp, then grind
  evalTactic (← `(tactic|
    (simp (config := { maxSteps := 200000 }) only [
      Lean.Grind.Algebra.algebraMap_add, Lean.Grind.Algebra.algebraMap_mul,
      Lean.Grind.Algebra.algebraMap_sub, Lean.Grind.Algebra.algebraMap_neg,
      Lean.Grind.Algebra.algebraMap_zero, Lean.Grind.Algebra.algebraMap_one,
      Lean.Grind.Algebra.algebraMap_smul_def];
     grind)))

end Macaulean.AlgPoly.Tactic
