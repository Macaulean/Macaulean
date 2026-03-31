# CAS Architecture Redesign

## Context

The `cas-architecture` branch established the right *ideas* — semantic CAS tasks, certificates, backend abstraction, chaining — but the implementation has structural problems:

- Every core type (`TaskKind`, `Judgment`, `Certificate`, `ArtifactKind`) is a closed enum that requires editing core files to extend
- A `Checkers.lean` / `Dischargers.lean` layer duplicates work the kernel already does
- The "chain" abstraction is used only for single-step calls
- User-facing tactics are hardwired to Macaulay2 with no dispatch
- No shared `cas` entry point

The redesign keeps what works (MRDI, serialization, M2 communication) and replaces the trust/execution layers with a strategy-based architecture where:

1. The **kernel owns all correctness** — the CAS is a data source, tactics construct proof terms
2. A single **`cas` tactic** dispatches to registered strategies based on goal shape
3. Strategies **decompose goals into small kernel-friendly steps**, guided by CAS data
4. A **per-invocation cache** memoizes backend calls across recursive subgoal processing
5. Strategies **register via `initialize`** (grind's `registerSolverExtension` pattern), enabling downstream extensibility

## Design

### MRDI Profile: Objects, Problems, Results

The MRDI profile has three layers. This separation is mathematically important — objects describe structures, problems describe computations, results describe what was computed.

Adding a new CAS tactic requires registering:
1. **MRDI types** — objects, problems, and results (via `MrdiType` instances)
2. **A backend handler** — for the problem `MrdiTypeDesc`s
3. **A strategy** — matches goals, builds MRDI problems, interprets MRDI results

The open set of `MrdiTypeDesc`s IS the capability vocabulary, replacing the closed `TaskKind` enum.

#### Layer 1: Mathematical Objects

Timeless mathematical structures. No computational parameters.

```lean
-- Coefficient domain: structured, not stringly-typed
inductive CoeffDomain where
  | nat | int | rat
  | primeField (p : Nat)
  | named (name : String) (params : Json := .null)
  deriving BEq, ToJson, FromJson

-- Polynomial ring: coefficient domain + variables. No monomial order — that's computational.
structure PolyRing where
  coeff : CoeffDomain
  vars : Array String         -- ["x", "y", "z"]
  deriving ToJson, FromJson, BEq

-- Ring element: polynomial data in a specific ring
structure RingElement where
  ring : PolyRing
  data : MRDI.PolynomialData

-- Ideal: generators in a specific ring
structure RingIdeal where
  ring : PolyRing
  generators : Array MRDI.PolynomialData
```

MRDI type descriptors identify the *kind* of object, not the specific instance. Ring context lives in the payload, not the type descriptor (because `MrdiType.mrdiType` is a class-level constant, not value-dependent):

```lean
instance : MrdiType RingElement where
  mrdiType := .string "ring_element"  -- identifies the kind
  decode? := ...                       -- ring context read from payload

instance : MrdiType RingIdeal where
  mrdiType := .string "ring_ideal"
  decode? := ...

instance : MrdiType ReductionProblem where
  mrdiType := .string "reduction_problem"
  decode? := ...
```

The ring context is carried in the JSON data field, not the type descriptor. `MRDI/Basic.lean` does not change.

#### Layer 2: CAS Problems

Computational requests. Bundle mathematical objects WITH algorithmic parameters (monomial orders, precision, solver choices). The problem IS the MRDI payload sent to the backend.

```lean
-- Monomial order: structured, not stringly-typed
inductive MonomialOrder where
  | lex | grlex | grevlex
  | named (name : String)
  deriving BEq, ToJson, FromJson

-- Polynomial reduction: element + ideal + computational choices
-- Monomial order belongs HERE, not in the ring definition
structure ReductionProblem where
  element : RingElement
  ideal : RingIdeal
  order : MonomialOrder := .grevlex   -- computational parameter
  -- other algorithmic hints...

-- Natural factorization
structure FactorizationProblem where
  n : Nat

-- SOS decomposition (future)
structure SOSProblem where
  element : RingElement
  -- SDP solver params, tolerance, etc.
```

#### Layer 3: CAS Results

What the backend computed and how. Rich enough for the handler to adapt.

```lean
-- Reduction result: quotients + remainder + method details
structure ReductionResult where
  method : String                        -- "groebner_basis", "direct", etc.
  quotients : Array MRDI.PolynomialData
  remainder : MRDI.PolynomialData
  -- for primary decomposition: recursive sub-results
  components : Option (Array ReductionResult) := none

-- Factorization result
structure FactorizationResult where
  factors : Array (Nat × Nat)            -- (prime, exponent) pairs
```

Each new mathematical operation adds its own MRDI types across all three layers — no core files touched.

### Backend Abstraction

```
Macaulean/CAS/Backend.lean
```

The backend layer manages **session lifecycle**, **MRDI dispatch**, and **failure semantics**. Adding a new backend should be easy: provide a process command, declare supported MRDI types, implement a request translator. The framework handles process management, mutex, timeout, and cleanup.

Design is grounded in two Lean core patterns:
- **BVDecide's `runInterruptible`** (`Lean/Elab/Tactic/BVDecide/External.lean`): per-request timeout with `IO.asTask` for async stream reads, `child.tryWait` polling, `killAndWait` cleanup
- **Watchdog's `FileWorker`** (`Lean/Server/Watchdog.lean`): `Std.Mutex WorkerState` state machine, lazy startup, graceful shutdown, dedicated forwarding tasks

#### What the backend implementor provides

Minimal: a process description and a request translator. No process management code.

```lean
-- Backend call outcomes — contract for implementors:
--   .unsupported: "I can't handle THIS request" (wrong ring, wrong order, unknown param).
--                 Dispatcher tries the next backend. Use for ALL payload-specific rejections.
--   .failure:     "Something broke" (process crashed, stream closed, decode error).
--                 Dispatcher propagates immediately. Reserved for transport/runtime faults.
inductive BackendResult where
  | ok (result : Mrdi)
  | unsupported (reason : String)        -- try next backend
  | failure (error : String)             -- propagate immediately

-- What a backend implementor provides
structure CASBackendDesc where
  name : Name
  priority : Nat := 1000
  supports : MrdiTypeDesc -> Bool        -- fast pre-filter on MRDI type kind
  -- Process configuration
  cmd : String                           -- e.g., "M2"
  args : Array String := #[]             -- e.g., #["--script", "./m2/macaulean.m2"]
  cwd : Option String := none
  requestTimeout : Nat := 30000          -- per-request timeout in ms
  -- The only thing the implementor writes: translate MRDI <-> backend protocol
  handleRequest : BackendStreams -> Mrdi -> IO BackendResult
```

`BackendStreams` is the stdin/stdout of the spawned process:

```lean
structure BackendStreams where
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream
```

#### What the framework provides

The framework manages everything else:

```lean
-- Session state machine (following Watchdog's FileWorker pattern)
inductive SessionState where
  | ready | running | terminating | crashed
  deriving BEq

-- A live session, framework-managed
structure CASSession where
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .inherit }
  streams : BackendStreams
  state : Std.Mutex SessionState          -- prevent shutdown races
  requestLock : Std.Mutex Unit            -- serialize request/response pairs
```

**Mutex-protected calls**: each request acquires `requestLock` so concurrent calls don't interleave I/O on the shared streams. Follows the Watchdog pattern where `Std.Mutex WorkerState` guards all state transitions.

**Per-request timeout**: wraps `handleRequest` in the BVDecide `runInterruptible` pattern — async stream reads via `IO.asTask`, polling with timeout budget, `killAndWait` cleanup if the process hangs.

**Graceful shutdown**: on cleanup, transitions state to `terminating`, kills process, waits. Like the Watchdog's `terminateFileWorker` sending `exit` before killing.

#### Registration

```lean
initialize casBackendsRef : IO.Ref (Array CASBackendDesc) <- IO.mkRef #[]

def registerCASBackend (desc : CASBackendDesc) : IO Unit := do
  unless (<- initializing) do
    throw (IO.userError "CAS backends can only be registered during initialization")
  casBackendsRef.modify (·.push desc)
```

#### Example: Macaulay2 Backend

The implementor provides only the process config and request translation:

```lean
initialize do
  registerCASBackend {
    name := `Macaulay2
    priority := 1000
    cmd := "M2"
    args := #["--script", "./macaulean.m2"]
    cwd := some "./m2/"
    requestTimeout := 30000
    supports := fun type => type ∈ [
      .string "reduction_problem",
      .string "factorization_problem"
    ]
    handleRequest := fun streams request => do
      -- Translate MRDI -> M2's JSON-RPC protocol
      match request.type with
      | .string "reduction_problem" =>
          let resp <- sendLspRequest streams "quotientRemainderPolyData" request.data
          pure (.ok (wrapAsResult resp))
      | .string "factorization_problem" =>
          let resp <- sendLspRequest streams "factorInt" request.data
          pure (.ok (wrapAsResult resp))
      | _ => pure (.unsupported "unknown request type")
  }
```

No process management, no mutex, no timeout handling. The framework does all of that. Adding Singular or SageMath is the same shape: different `cmd`/`args`, different `handleRequest` translation.

#### Session Management in CASContext

Sessions are long-lived (expensive to start), lazy (started on first call), and cleaned up when `cas` returns:

```lean
structure LiveBackend where
  desc : CASBackendDesc
  session : Std.Mutex (Option CASSession)  -- lazily initialized, mutex-protected

structure CASContext where
  backends : Array LiveBackend             -- sorted by (priority, name)
  cache : IO.Ref CASCache

-- Lazy session startup with dead-session detection
-- If stored session is crashed/terminated, clear it and respawn
def LiveBackend.getSession (lb : LiveBackend) : IO CASSession :=
  lb.session.atomically do
    match (<- get) with
    | some s =>
        if (<- isSessionAlive s) then pure s
        else do
          shutdownSession s                -- clean up dead session
          let s <- spawnSession lb.desc
          set (some s)
          pure s
    | none =>
        let s <- spawnSession lb.desc
        set (some s)
        pure s

-- Cleanup all sessions when cas tactic finishes
def CASContext.cleanup (ctx : CASContext) : IO Unit := do
  for lb in ctx.backends do
    lb.session.atomically do
      if let some session := (<- get) then
        shutdownSession session
        set none
```

Strategies never reference backends directly — they call `ctx.call request` and the framework handles session lifecycle, dispatch, timeout, and cleanup.

### Core Types

```
Macaulean/CAS/Strategy.lean
```

```lean
structure CASCache where
  results : Std.HashMap UInt64 (Json × Mrdi)  -- hash(request) -> (full request, response); equality-checked on hit

structure CASContext where
  backends : Array LiveBackend             -- all registered backends, sorted by (priority, name)
  cache : IO.Ref CASCache                 -- memoized backend calls

-- Strategy sends an MRDI problem; context finds a backend by MrdiTypeDesc + caches.
-- Backends pre-sorted by priority. Falls through on `unsupported`; `failure` propagates immediately.
-- Cache is collision-safe: equality-checked on hit.
def CASContext.call (ctx : CASContext) (request : Mrdi) : IO Mrdi := do
  let requestJson := toJson request
  let key := hash requestJson
  if let some (cachedReq, cachedResult) := (<- ctx.cache.get).results[key]? then
    if cachedReq == requestJson then return cachedResult
  let candidates := ctx.backends.filter (·.supports request.type)
  if candidates.isEmpty then
    throw (IO.userError s!"No backend supports MRDI type: {request.type}")
  for backend in candidates do
    match (<- backend.call request) with
    | .ok result =>
        ctx.cache.modify fun c =>
          { c with results := c.results.insert key (requestJson, result) }
        return result
    | .unsupported _ => continue            -- try next backend
    | .failure err =>                        -- operational error: propagate immediately
        throw (IO.userError s!"Backend {backend.name} failed: {err}")
  throw (IO.userError s!"All backends reported unsupported for type: {request.type}")

structure CASStrategyEntry where
  name : Name
  priority : Nat := 1000                  -- lower = tried first (like simp)
  match? : MVarId -> MetaM Bool           -- can this strategy handle this goal?
  execute : CASContext -> MVarId -> TacticM (List MVarId)  -- returns remaining subgoals
```

### Strategy Registration

Following grind's `registerSolverExtension` pattern:

```lean
initialize casStrategiesRef : IO.Ref (Array CASStrategyEntry) <- IO.mkRef #[]

def registerCASStrategy (entry : CASStrategyEntry) : IO Unit := do
  unless (<- initializing) do
    throw (IO.userError "CAS strategies can only be registered during initialization")
  casStrategiesRef.modify (·.push entry)
```

Downstream packages register in their own `initialize` blocks:

```lean
-- In a downstream package
initialize do
  registerCASStrategy {
    name := `myStrategy
    match? := fun goal => ...
    execute := fun ctx goal => ...
  }
```

### The `cas` Tactic

```
Macaulean/CAS/Tactic.lean
```

```lean
structure CASLoopState where
  attempted : Std.HashSet (MVarId × Name)  -- (goal, strategy) pairs already tried
  fuel : Nat                                -- remaining recursion budget

def casLoop (ctx : CASContext) (state : IO.Ref CASLoopState)
    (goals : List MVarId) : TacticM (List MVarId) := do
  let strategies <- casStrategiesRef.get
  let strategies := strategies.qsort fun a b => (a.priority, a.name.toString) < (b.priority, b.name.toString)
  let mut remaining := []
  for goal in goals do
    if <- goal.isAssigned then continue
    let s <- state.get
    if s.fuel == 0 then
      remaining := remaining ++ [goal]
      continue
    match <- tryStrategies ctx state strategies goal with
    | some subgoals =>
        state.modify fun s => { s with fuel := s.fuel - 1 }
        remaining := remaining ++ (<- casLoop ctx state subgoals)
    | none =>
        remaining := remaining ++ [goal]
  return remaining

elab "cas" : tactic => do
  let ctx <- mkCASContext
  let state <- IO.mkRef { attempted := {}, fuel := 100 }
  try
    let remaining <- casLoop ctx state [<- getMainGoal]
    replaceMainGoal remaining
  finally
    ctx.cleanup                            -- always kill backend processes, even on failure
```

`tryStrategies` skips any `(goal, strategy)` pair already in `state.attempted`, preventing trivial loops. The fuel budget caps total recursion depth. `try`/`finally` guarantees `ctx.cleanup` runs — no leaked child processes on success, failure, or exception. **Strategies own their own closing tactics** — if a strategy produces an equality subgoal, it is the strategy's responsibility to call `ring`/`grind`/etc. internally before returning remaining subgoals. The loop does not have a fallback chain. Goals that no strategy matches are left for the user.

### Strategy Example: Ideal Membership

The strategy builds an MRDI Problem, sends it, interprets the MRDI Result.

```lean
initialize do
  registerCASStrategy {
    name := `idealMembership
    priority := 1000
    match? := fun goal => do
      let target <- goal.getType
      return target.isAppOf ``Macaulean.InIdeal
    execute := fun ctx goal => do
      -- 1. Reify goal -> mathematical objects (RingElement, RingIdeal)
      -- 2. Build MRDI problem:
      --      let problem := toMrdi (ReductionProblem { element, ideal, order := "grevlex" })
      -- 3. ctx.call problem  (dispatched by MrdiTypeDesc, backend-neutral, cached)
      -- 4. Deserialize result:
      --      let result <- fromMrdi? response (alpha := ReductionResult)
      -- 5. Match on result.method / structure:
      --      direct reduction -> use quotients as existential witnesses, close with ring
      --      primary decomposition -> recurse on result.components
      -- 6. Strategy owns all closing tactics (simp, grind, ring, etc.)
      -- 7. Return [] (fully closed) or remaining subgoals
  }
```

### Strategy Example: Factorization / Reducibility

```lean
initialize do
  registerCASStrategy {
    name := `reducibility
    priority := 1000
    match? := fun goal => do
      let target <- goal.getType
      -- match not Irreducible n
      ...
    execute := fun ctx goal => do
      -- 1. Extract n from goal
      -- 2. let problem := toMrdi (FactorizationProblem { n })
      -- 3. let response <- ctx.call problem
      -- 4. let result <- fromMrdi? response (alpha := FactorizationResult)
      -- 5. Rewrite goal using result.factors
      -- 6. Close n = p1^e1 * ... via decide (strategy owns this)
      -- 7. Close not (IsUnit ...) via grind (strategy owns this)
      -- 8. Return [] or remaining subgoals
  }
```

Strategies build MRDI problems (objects + computational params), call `ctx.call` (backend-neutral, auto-cached), interpret MRDI results (data + method details), and own all closing tactics. The `cas` loop only recurses with CAS strategies.

## File Changes

### Keep unchanged
- `MRDI/Basic.lean` — MRDI container format
- `MRDI/Poly.lean` — polynomial data types
- `Macaulean/Serialize.lean` — polynomial serialization/deserialization

### Remove
- `Macaulean/CAS/Semantics.lean` — `Judgment`, `Certificate`, `ArtifactRef`, `Provenance`, etc.
- `Macaulean/CAS/Chain.lean` — `ChainState`, `ChainStep`, `ArtifactStore`
- `Macaulean/CAS/Execution.lean` — `executeStep`
- `Macaulean/CAS/Checkers.lean` — certificate checkers
- `Macaulean/CAS/Dischargers.lean` — judgment dischargers
- `Macaulean/CAS/Macaulay2Backend.lean` — backend wrapper, helper functions

### New files (replacing old Backend.lean entirely)
- `Macaulean/CAS/Backend.lean` — `CASBackend`, backend registration (replaces old TaskKind/Capability version)
- `Macaulean/CAS/Strategy.lean` — `CASStrategyEntry`, `CASContext`, `CASCache`, strategy registration
- `Macaulean/CAS/Tactic.lean` — `cas` tactic, `casLoop`
- `Macaulean/CAS/Reify.lean` — shared polynomial reification (extracted from IdealMembership.lean)

### Rework
- `Macaulean/Macaulay2.lean` — rewrite as a `registerCASBackend` call with `handleRequest` translator; remove `globalM2Server` and manual process management
- `Macaulean/IdealMembership.lean` — keep `InIdeal`, `linearCombination` definitions; rework tactic into a registered strategy
- `Macaulean/Factorization.lean` — keep `IsUnit`, `Irreducible` definitions; rework tactics into registered strategies
- `Macaulean/CAS.lean` — update to re-export the new modules
- `MacauleanTest/CASBackend.lean` — rewrite: test strategy registration + `cas` tactic
- `MacauleanTest/CASChain.lean` — remove or replace with cache tests
- `MacauleanTest/IdealMembership.lean` — update to use `cas` instead of `m2ideal_member`
- `MacauleanTest/Factorization.lean` — update to use `cas` instead of `m2factor`/`m2reducible`

## Implementation Order

1. **Enrich MRDI profile** — `CoeffDomain`, `MonomialOrder`, `PolyRing`, `RingElement`, `RingIdeal`, `ReductionProblem`, `ReductionResult`, `FactorizationProblem`, `FactorizationResult`
2. **`Macaulean/CAS/Backend.lean`** — `CASBackendDesc`, `CASSession`, `BackendResult`, `LiveBackend`, session lifecycle (mutex, timeout, cleanup), registration
3. **`Macaulean/CAS/Strategy.lean`** — `CASStrategyEntry`, `CASContext`, `CASCache`, strategy registration
4. **Rework `Macaulean/Macaulay2.lean`** — rewrite as `registerCASBackend` with `handleRequest`; remove `globalM2Server`
5. **`Macaulean/CAS/Reify.lean`** — shared polynomial reification (goal -> MRDI objects)
6. **`Macaulean/CAS/Tactic.lean`** — `cas` tactic + `casLoop` with fuel/cycle detection
7. **Rework `Macaulean/IdealMembership.lean`** — convert to registered strategy
8. **Rework `Macaulean/Factorization.lean`** — convert to registered strategies
9. **Update `Macaulean/CAS.lean`** — re-export new modules
10. **Remove old CAS files** — Semantics, Chain, Execution, Checkers, Dischargers, Macaulay2Backend
11. **Update tests** — rewrite to use `cas` tactic
12. **Update `CAS_ARCHITECTURE.md`** — reflect new design

## Verification

- `lake build MacauleanTest` passes
- Tests use `cas` directly (not old tactic names)
- Ideal membership: `cas` closes `InIdeal (x^2 - y) [x^2 - y, y^2]`
- Factorization: `cas` closes `not Irreducible 60`
- Non-member correctly fails
- Old tactics (`m2ideal_member`, `m2factor`, `m2reducible`) kept as thin wrappers, still work

## Decided

- **Old tactics**: kept as thin wrappers around the strategy system; tests use `cas`
- **Closing tactics**: strategies own their closers (no fallback chain in `cas` loop)
- **Priority**: lower number = tried first (like simp), default 1000
- **MRDI end-to-end**: backend protocol uses typed `Mrdi` objects (dispatch on `MrdiTypeDesc`), not raw JSON/strings
- **Three-layer MRDI profile**: Objects (math structures, no computational params) / Problems (objects + algorithmic params like monomial order) / Results (data + method details). Monomial orders belong to problems, not ring definitions.
- **Rich results**: backend responses carry computation details (method, intermediate data). No proof sketch — handler owns proof construction
- **Backend abstraction**: backends register with `MrdiTypeDesc`s they support; strategies never reference backends directly
- **MRDI types as vocabulary**: the open set of `MrdiTypeDesc`s replaces the closed `TaskKind` enum. New operations = new MRDI types, registered alongside their strategy and backend handler

- **MRDI type descriptors are kind-level, not value-level**: `MrdiType.mrdiType` is a class constant. Ring context, monomial orders, and other instance-specific data go in the payload, not the type descriptor. `MRDI/Basic.lean` does not change.
- **Structured domain/order types**: `CoeffDomain` and `MonomialOrder` are structured inductives (with `named` escape hatches), not free-form strings. Prevents undocumented string conventions.
- **Discriminated backend results**: `BackendResult` = `ok | unsupported | failure`. Dispatcher falls through only on `unsupported`; `failure` propagates immediately with backend name and error. No silent failure masking.
- **Backend priority + fallthrough**: backends have priority numbers. `CASContext.call` tries matching backends in priority order on `unsupported`. Deterministic, import-order-independent.
- **Deterministic tie-breaking**: strategies and backends sorted by `(priority, name)`. No import-order dependence at equal priority.
- **Progress guard**: `casLoop` tracks attempted `(goal, strategy)` pairs and has a fuel budget. Prevents non-termination from buggy strategies.
- **Collision-safe cache**: cache keyed by `(hash, full request Json)`, equality-checked on hit. No silent cross-goal aliasing.
- **Guaranteed cleanup**: `cas` tactic uses `try`/`finally` so `ctx.cleanup` always runs. No leaked child processes.
- **Dead session respawn**: `getSession` checks if stored session is alive; respawns on crash/timeout instead of reusing dead session.
- **Clear unsupported/failure contract**: `.unsupported` for ALL payload-specific rejections (wrong ring, params); `.failure` reserved for transport/runtime faults only. Backend implementors must use `.unsupported` for capability mismatches.
- **Backend lifecycle is framework-managed**: implementor provides `cmd`/`args`/`handleRequest`; framework owns process spawn, mutex, timeout, cleanup. Based on BVDecide's `runInterruptible` and Watchdog's `FileWorker` patterns from Lean core.

## Known Limitations / Future Work

## Open / Still Discussing

- Whether the MRDI result should carry execution-level detail (proof plans) or just computation details. Current decision: computation details only, handler owns proof construction. May revisit.
- Cache scope beyond backend call memoization — whether richer state-passing between parent/child strategies is needed.
