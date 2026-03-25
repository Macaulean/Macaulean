import Macaulean.CAS

open Macaulean.CAS

def chainInput : StoredArtifact :=
  { ref := { id := "chain:nat:15" }
    artifact := Artifact.ofValue .scalar (15 : Nat) }

def chainStore : ArtifactStore :=
  ArtifactStore.insert emptyArtifactStore chainInput

def resolvedFactorRequest : Except String ResolvedTaskRequest :=
  TaskRequest.resolve?
    { task := TaskKind.factor
      inputs := #[chainInput.ref] }
    chainStore

#guard match resolvedFactorRequest with
  | .ok request => request.inputs.size == 1
  | .error _ => false

def unresolvedFactorRequest : Except String ResolvedTaskRequest :=
  TaskRequest.resolve?
    { task := TaskKind.factor
      inputs := #[{ id := "missing" }] }
    chainStore

#guard match unresolvedFactorRequest with
  | .ok _ => false
  | .error _ => true

def recordedState : ChainState :=
  (ChainState.recordArtifacts {} #[chainInput]).recordResult {
    status := TaskStatus.success
    artifacts := #[]
    judgments := #[Judgment.nonnegativity chainInput.ref]
    certificates := #[]
  }

#guard recordedState.artifacts.find? chainInput.ref |>.isSome
#guard recordedState.judgments.size == 1

def derivedState : ChainState :=
  recordedState.recordDerivedJudgments #[Judgment.nonnegativity chainInput.ref]

#guard derivedState.derivedJudgments.size == 1
