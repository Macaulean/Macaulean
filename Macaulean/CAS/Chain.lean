import Macaulean.CAS.Backend

namespace Macaulean.CAS

abbrev ArtifactStore := Std.TreeMap ArtifactId StoredArtifact

def emptyArtifactStore : ArtifactStore := .empty

def ArtifactStore.insert (store : ArtifactStore) (artifact : StoredArtifact) : ArtifactStore :=
  Std.TreeMap.insert store artifact.ref.id artifact

def ArtifactStore.insertMany (store : ArtifactStore) (artifacts : Array StoredArtifact) : ArtifactStore :=
  artifacts.foldl (init := store) fun acc artifact => acc.insert artifact

def ArtifactStore.find? (store : ArtifactStore) (ref : ArtifactRef) : Option StoredArtifact :=
  store.get? ref.id

def ArtifactStore.resolveInputs? (store : ArtifactStore) (refs : Array ArtifactRef) :
    Except String (Array StoredArtifact) := do
  let mut resolved := #[]
  for ref in refs do
    let some artifact := store.find? ref
      | .error s!"Unknown artifact ref: {ref.id}"
    resolved := resolved.push artifact
  pure resolved

def TaskRequest.resolve? (request : TaskRequest) (store : ArtifactStore) :
    Except String ResolvedTaskRequest := do
  let inputs ← store.resolveInputs? request.inputs
  pure {
    task := request.task
    inputs := inputs
    parameters := request.parameters
  }

structure CheckerName where
  name : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure DischargerName where
  name : String
  deriving Repr, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

structure ChainStep where
  label? : Option String := none
  backend : String
  request : TaskRequest
  checker? : Option CheckerName := none
  discharger? : Option DischargerName := none
  deriving Lean.ToJson, Lean.FromJson

structure ChainState where
  artifacts : ArtifactStore := emptyArtifactStore
  judgments : Array Judgment := #[]
  checkedJudgments : Array Judgment := #[]
  derivedJudgments : Array Judgment := #[]
  certificates : Array Certificate := #[]

def ChainState.recordArtifacts (state : ChainState) (artifacts : Array StoredArtifact) : ChainState :=
  { state with artifacts := state.artifacts.insertMany artifacts }

def ChainState.recordResult (state : ChainState) (result : TaskResult) : ChainState :=
  { artifacts := state.artifacts.insertMany result.artifacts
    judgments := state.judgments ++ result.judgments
    checkedJudgments := state.checkedJudgments
    derivedJudgments := state.derivedJudgments
    certificates := state.certificates ++ result.certificates }

def ChainState.recordCheckedJudgment (state : ChainState) (judgment : Judgment) : ChainState :=
  if state.checkedJudgments.any (· == judgment) then state
  else { state with checkedJudgments := state.checkedJudgments.push judgment }

def ChainState.recordCheckedJudgments (state : ChainState) (judgments : Array Judgment) : ChainState :=
  judgments.foldl (init := state) fun acc judgment => acc.recordCheckedJudgment judgment

def ChainState.recordDerivedJudgment (state : ChainState) (judgment : Judgment) : ChainState :=
  if state.derivedJudgments.any (· == judgment) then state
  else { state with derivedJudgments := state.derivedJudgments.push judgment }

def ChainState.recordDerivedJudgments (state : ChainState) (judgments : Array Judgment) : ChainState :=
  judgments.foldl (init := state) fun acc judgment => acc.recordDerivedJudgment judgment

instance : MrdiType CheckerName where
  mrdiType := .string "Macaulean.CAS.CheckerName"
  decode? := trivialDecode? (.string "Macaulean.CAS.CheckerName")

instance : MrdiType DischargerName where
  mrdiType := .string "Macaulean.CAS.DischargerName"
  decode? := trivialDecode? (.string "Macaulean.CAS.DischargerName")

instance : MrdiType ChainStep where
  mrdiType := .string "Macaulean.CAS.ChainStep"
  decode? := trivialDecode? (.string "Macaulean.CAS.ChainStep")

end Macaulean.CAS
