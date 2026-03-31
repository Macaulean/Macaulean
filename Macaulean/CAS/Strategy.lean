import Lean
import Macaulean.CAS.Backend

open Lean Meta Elab Tactic Json

namespace Macaulean.CAS

/-! # CAS Strategy Framework

Strategy registration, CAS context with caching, and MRDI dispatch.
-/

-- ============================================================================
-- Cache
-- ============================================================================

structure CASCache where
  results : Std.HashMap UInt64 (Json × Mrdi) := {}

-- ============================================================================
-- CAS Context
-- ============================================================================

structure CASContext where
  backends : Array LiveBackend
  cache : IO.Ref CASCache

def mkCASContext : IO CASContext := do
  let descs ← getRegisteredBackends
  let descs := descs.qsort fun a b =>
    a.priority < b.priority || (a.priority == b.priority && a.name.toString < b.name.toString)
  let backends ← descs.mapM LiveBackend.new
  let cache ← IO.mkRef {}
  pure { backends, cache }

/-- Dispatch an MRDI request to the first supporting backend, with caching.
Falls through on `.unsupported`; propagates `.failure` immediately. -/
def CASContext.call (ctx : CASContext) (request : Mrdi) : IO Mrdi := do
  let requestJson := toJson request
  let key := hash requestJson
  let cache ← ctx.cache.get
  if let some (cachedReq, cachedResult) := cache.results[key]? then
    if cachedReq == requestJson then return cachedResult
  let candidates := ctx.backends.filter (·.supports request.type)
  if candidates.isEmpty then
    throw (IO.userError s!"No backend supports MRDI type: {toJson request.type}")
  for backend in candidates do
    match ← backend.call request with
    | .ok result =>
        ctx.cache.modify fun c =>
          { c with results := c.results.insert key (requestJson, result) }
        return result
    | .unsupported _ => continue
    | .failure err =>
        throw (IO.userError s!"Backend {backend.desc.name} failed: {err}")
  throw (IO.userError s!"All backends reported unsupported for type: {toJson request.type}")

/-- Clean up all backend sessions. -/
def CASContext.cleanup (ctx : CASContext) : IO Unit := do
  for lb in ctx.backends do
    lb.shutdown

-- ============================================================================
-- Strategy Entry
-- ============================================================================

structure CASStrategyEntry where
  name : Name
  priority : Nat := 1000
  match? : MVarId → MetaM Bool
  execute : CASContext → MVarId → TacticM (List MVarId)

-- ============================================================================
-- Strategy Registration
-- ============================================================================

initialize casStrategiesRef : IO.Ref (Array CASStrategyEntry) ← IO.mkRef #[]

def registerCASStrategy (entry : CASStrategyEntry) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "CAS strategies can only be registered during initialization")
  casStrategiesRef.modify (·.push entry)

def getRegisteredStrategies : IO (Array CASStrategyEntry) :=
  casStrategiesRef.get

end Macaulean.CAS
