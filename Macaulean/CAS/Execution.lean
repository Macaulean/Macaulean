import Macaulean.CAS.Dischargers

namespace Macaulean.CAS

def runCertificatesWithChecker (state : ChainState) (checkerName : CheckerName)
    (certificates : Array Certificate) : Except String (Array Judgment) := do
  let some checker := findCertificateChecker? checkerName
    | .error s!"Unknown certificate checker: {checkerName.name}"
  let mut judgments := #[]
  for certificate in certificates do
    let judgment ← CertificateChecker.check checker state certificate
    judgments := judgments.push judgment
  pure judgments

def runJudgmentsWithDischarger (state : ChainState) (dischargerName : DischargerName)
    (judgments : Array Judgment) : Except String (Array Judgment) := do
  let some discharger := findJudgmentDischarger? dischargerName
    | .error s!"Unknown judgment discharger: {dischargerName.name}"
  JudgmentDischarger.discharge discharger state judgments

def executeStep [BackendSession σ] (session : σ) (state : ChainState)
    (step : ChainStep) : IO (Except String ChainState) := do
  if BackendSession.name session != step.backend then
    pure <| .error s!"Step backend mismatch: expected {step.backend}, got {BackendSession.name session}"
  else
    match step.request.resolve? state.artifacts with
    | .error err => pure <| .error err
    | .ok request =>
        let result ← BackendSession.runTask session request
        if result.status != TaskStatus.success then
          pure <| .error <| result.message?.getD s!"Backend step failed with status {reprStr result.status}"
        else
          let nextState := state.recordResult result
          match step.checker? with
          | none =>
              pure <| .ok nextState
          | some checkerName =>
              pure <| do
                let checkedJudgments ←
                  runCertificatesWithChecker nextState checkerName result.certificates
                let checkedState := nextState.recordCheckedJudgments checkedJudgments
                match step.discharger? with
                | none =>
                    pure checkedState
                | some dischargerName =>
                    let derivedJudgments ←
                      runJudgmentsWithDischarger checkedState dischargerName checkedJudgments
                    pure <| checkedState.recordDerivedJudgments derivedJudgments

end Macaulean.CAS
