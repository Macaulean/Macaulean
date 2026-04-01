import Macaulean

open Macaulean
open Macaulean.CAS
open MRDI.CAS

namespace MacauleanTest.PermGroup

def requireIO (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

-- ============================================================================
-- Kernel-verified: cas calls GAP, gets word, resolves to concrete permutations,
-- decide verifies the composition. No Perm.inv in kernel path.
-- ============================================================================

def g1_3 : Perm 3 := ⟨#[1, 0, 2], by decide⟩  -- (0 1)
def g2_3 : Perm 3 := ⟨#[0, 2, 1], by decide⟩  -- (1 2)
def target_3 : Perm 3 := ⟨#[1, 2, 0], by decide⟩  -- (0 1 2)

-- CAS finds the decomposition, kernel verifies composition
example : InPermGroup target_3 #[g1_3, g2_3] := by cas

-- ============================================================================
-- Backend-level tests
-- ============================================================================

-- (1 3)(2 4) in S₄ = <(1 2), (1 2 3 4)>
#eval do
  let descs ← getRegisteredBackends
  let oscarDescs := descs.filter fun (b : CASBackendDesc) => b.name == `Oscar
  let backends ← oscarDescs.mapM fun d => LiveBackend.new d
  let cache ← IO.mkRef ({} : CASCache)
  let ctx : CASContext := { backends, cache }
  try
    let problem : PermGroupMembershipProblem := {
      size := 4
      generators := #[#[2, 1, 3, 4], #[2, 3, 4, 1]]
      target := #[3, 4, 1, 2]
    }
    let response ← ctx.call (toMrdi problem)
    let result ← match fromMrdi? (α := PermGroupMembershipResult) response with
      | .ok (r : PermGroupMembershipResult) => pure r
      | .error e => throw <| IO.userError s!"decode failed: {e}"
    requireIO result.inGroup "(1 3)(2 4) should be in S₄"
    requireIO (result.word.size > 0) "should return a non-empty word"
  finally
    ctx.cleanup

end MacauleanTest.PermGroup
