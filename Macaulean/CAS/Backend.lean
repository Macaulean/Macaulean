import MRDI.Basic
import MRDI.CAS

open Lean Json

namespace Macaulean.CAS

/-! # CAS Backend Framework

Framework-managed backend sessions with lifecycle and dispatch.
Backend implementors provide: process config + request translator.
Framework provides: spawn, request serialization, cleanup.

Design based on:
- BVDecide's `runInterruptible` (timeout, async reads, killAndWait)
- Watchdog's `FileWorker` (state machine, lazy startup, graceful shutdown)
-/

-- ============================================================================
-- Backend Result
-- ============================================================================

/-- Backend call outcomes.
- `.unsupported`: "I can't handle THIS request" (wrong ring, unknown param). Dispatcher tries next.
  Use for ALL payload-specific rejections.
- `.failure`: "Something broke" (crash, stream closed, decode error). Propagates immediately.
  Reserved for transport/runtime faults only. -/
inductive BackendResult where
  | ok (result : Mrdi)
  | unsupported (reason : String)
  | failure (error : String)

-- ============================================================================
-- Backend Streams
-- ============================================================================

structure BackendStreams where
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream

-- ============================================================================
-- Session State Machine
-- ============================================================================

inductive SessionState where
  | ready
  | running
  | terminating
  | crashed
  deriving BEq

-- ============================================================================
-- Backend Description (what the implementor provides)
-- ============================================================================

/-- What a backend implementor provides. No process management code needed. -/
structure CASBackendDesc where
  name : Name
  priority : Nat := 1000
  supports : MrdiTypeDesc → Bool
  cmd : String
  args : Array String := #[]
  cwd : Option String := none
  requestTimeout : Nat := 30000
  handleRequest : BackendStreams → Mrdi → IO BackendResult

-- ============================================================================
-- CAS Session (framework-managed)
-- ============================================================================

structure CASSession where
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .inherit }
  streams : BackendStreams
  state : IO.Ref SessionState
  busy : IO.Ref Bool

-- ============================================================================
-- Session lifecycle
-- ============================================================================

def spawnSession (desc : CASBackendDesc) : IO CASSession := do
  let child ← IO.Process.spawn {
    cmd := desc.cmd
    args := desc.args
    cwd := desc.cwd
    stdin := .piped
    stdout := .piped
    stderr := .inherit
  }
  let (stdinHandle, child) ← child.takeStdin
  let stdinStream := IO.FS.Stream.ofHandle stdinHandle
  let stdoutStream := IO.FS.Stream.ofHandle child.stdout
  let state ← IO.mkRef SessionState.ready
  let busy ← IO.mkRef false
  pure { child, streams := { stdin := stdinStream, stdout := stdoutStream }, state, busy }

def isSessionAlive (session : CASSession) : IO Bool := do
  match ← session.state.get with
  | .ready | .running => pure true
  | .terminating | .crashed => pure false

def shutdownSession (session : CASSession) : IO Unit := do
  session.state.set .terminating
  try session.child.kill catch _ => pure ()
  let _ ← session.child.wait
  pure ()

/-- Serialize request/response pairs on the shared streams. -/
def withRequestLock (session : CASSession) (action : IO α) : IO α := do
  while ← session.busy.modifyGet fun b => (b, true) do
    IO.sleep 1
  try
    let result ← action
    session.busy.set false
    pure result
  catch e =>
    session.busy.set false
    throw e

-- ============================================================================
-- Live Backend (lazy session)
-- ============================================================================

structure LiveBackend where
  desc : CASBackendDesc
  session : IO.Ref (Option CASSession)

def LiveBackend.new (desc : CASBackendDesc) : IO LiveBackend := do
  let session ← IO.mkRef none
  pure { desc, session }

def LiveBackend.getSession (lb : LiveBackend) : IO CASSession := do
  match ← lb.session.get with
  | some s =>
      if ← isSessionAlive s then pure s
      else do
        shutdownSession s
        let s ← spawnSession lb.desc
        lb.session.set (some s)
        pure s
  | none =>
      let s ← spawnSession lb.desc
      lb.session.set (some s)
      pure s

def LiveBackend.call (lb : LiveBackend) (request : Mrdi) : IO BackendResult := do
  let session ← lb.getSession
  session.state.set .running
  try
    let result ← withRequestLock session (lb.desc.handleRequest session.streams request)
    session.state.set .ready
    pure result
  catch e =>
    session.state.set .crashed
    pure (.failure s!"Backend {lb.desc.name} crashed: {e}")

def LiveBackend.shutdown (lb : LiveBackend) : IO Unit := do
  if let some session := ← lb.session.get then
    shutdownSession session
    lb.session.set none

def LiveBackend.supports (lb : LiveBackend) (type : MrdiTypeDesc) : Bool :=
  lb.desc.supports type

-- ============================================================================
-- Backend Registration
-- ============================================================================

initialize casBackendsRef : IO.Ref (Array CASBackendDesc) ← IO.mkRef #[]

def registerCASBackend (desc : CASBackendDesc) : IO Unit := do
  unless (← initializing) do
    throw (IO.userError "CAS backends can only be registered during initialization")
  casBackendsRef.modify (·.push desc)

def getRegisteredBackends : IO (Array CASBackendDesc) :=
  casBackendsRef.get

end Macaulean.CAS
