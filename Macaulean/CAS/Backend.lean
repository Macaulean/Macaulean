import Macaulean.CAS.Semantics

open Lean Json

namespace Macaulean.CAS

inductive TaskKind where
  | normalize
  | factor
  | reduce
  | quotientRemainder
  | groebnerBasis
  | sumOfSquares
  | eliminate
  | solve
  | backendSpecific (name : String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure Capability where
  task : TaskKind
  exact : Bool := true
  certificateBearing : Bool := false
  deterministic : Bool := true
  inputKinds : Array ArtifactKind := #[]
  outputKinds : Array ArtifactKind := #[]
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure TaskRequest where
  task : TaskKind
  inputs : Array ArtifactRef
  parameters : Json := .null
  deriving BEq, ToJson, FromJson

structure ResolvedTaskRequest where
  task : TaskKind
  inputs : Array StoredArtifact
  parameters : Json := .null
  deriving ToJson, FromJson

inductive TaskStatus where
  | success
  | failure
  | unknown
  | unsupported
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure TaskResult where
  status : TaskStatus
  artifacts : Array StoredArtifact := #[]
  judgments : Array Judgment := #[]
  certificates : Array Certificate := #[]
  provenance? : Option Provenance := none
  message? : Option String := none
  deriving ToJson, FromJson

class BackendSession (σ : Type) where
  name : σ → String
  capabilities : σ → IO (Array Capability)
  runTask : σ → ResolvedTaskRequest → IO TaskResult

structure BackendFactory where
  Session : Type
  start : IO Session
  stop : Session → IO Unit
  deriving Inhabited

instance : MrdiType TaskKind where
  mrdiType := .string "Macaulean.CAS.TaskKind"
  decode? := trivialDecode? (.string "Macaulean.CAS.TaskKind")

instance : MrdiType Capability where
  mrdiType := .string "Macaulean.CAS.Capability"
  decode? := trivialDecode? (.string "Macaulean.CAS.Capability")

instance : MrdiType TaskRequest where
  mrdiType := .string "Macaulean.CAS.TaskRequest"
  decode? := trivialDecode? (.string "Macaulean.CAS.TaskRequest")

instance : MrdiType ResolvedTaskRequest where
  mrdiType := .string "Macaulean.CAS.ResolvedTaskRequest"
  decode? := trivialDecode? (.string "Macaulean.CAS.ResolvedTaskRequest")

instance : MrdiType TaskStatus where
  mrdiType := .string "Macaulean.CAS.TaskStatus"
  decode? := trivialDecode? (.string "Macaulean.CAS.TaskStatus")

instance : MrdiType TaskResult where
  mrdiType := .string "Macaulean.CAS.TaskResult"
  decode? := trivialDecode? (.string "Macaulean.CAS.TaskResult")

end Macaulean.CAS
