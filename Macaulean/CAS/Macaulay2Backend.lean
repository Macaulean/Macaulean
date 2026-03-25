import Macaulean.CAS.Backend
import Macaulean.CAS.Chain
import Macaulean.CAS.Checkers
import Macaulean.CAS.Execution
import Macaulean.Macaulay2
import MRDI.Poly

open Lean Json

namespace Macaulean.CAS

abbrev M2Child := IO.Process.Child {stdin := .null, stdout := .piped, stderr := .inherit}

structure Macaulay2Session where
  child? : Option M2Child := none
  server : Macaulay2
  nextArtifactId : IO.Ref Nat

structure CheckedQuotientRemainder where
  quotients : Array MRDI.Poly
  remainder : MRDI.Poly
  quotientRemainderJudgment : Judgment
  idealMembershipJudgment? : Option Judgment := none

structure CheckedSumOfSquares where
  scale : Nat
  summands : Array SumOfSquaresSummand
  sumOfSquaresJudgment : Judgment
  nonnegativityJudgment? : Option Judgment := none

def Macaulay2Session.start : IO Macaulay2Session := do
  let (child, server) ← startM2Server
  let nextArtifactId ← IO.mkRef 0
  pure { child? := some child, server, nextArtifactId }

def Macaulay2Session.fromServer (server : Macaulay2) : IO Macaulay2Session := do
  let nextArtifactId ← IO.mkRef 0
  pure { server, nextArtifactId }

def globalMacaulay2Session : IO Macaulay2Session := do
  Macaulay2Session.fromServer (← globalM2Server)

def Macaulay2Session.stop (session : Macaulay2Session) : IO Unit := do
  let _ := session
  pure ()

def macaulay2Provenance (task : String) : Provenance :=
  { backend := "Macaulay2", task := task, deterministic := true }

def Macaulay2Session.freshRef (session : Macaulay2Session) (label : String) : IO ArtifactRef := do
  let n ← session.nextArtifactId.modifyGet fun n => (n, n + 1)
  pure { id := s!"m2:{label}:{n}" }

def Macaulay2Session.mkStoredArtifact [MrdiType α] (session : Macaulay2Session)
    (label : String) (kind : ArtifactKind) (value : α) (task : String) : IO StoredArtifact := do
  let ref ← session.freshRef label
  pure {
    ref := ref
    artifact := Artifact.ofValue kind value (some <| macaulay2Provenance task)
  }

private def numVarsOfPolynomialData (polyData : MRDI.PolynomialData) : Nat :=
  polyData.foldl (init := 0) fun acc term =>
    term.mon.foldl (init := acc) fun acc power => max acc (power.x + 1)

def Macaulay2Session.factorTask (session : Macaulay2Session)
    (request : ResolvedTaskRequest) : IO TaskResult := do
  let some target := request.inputs[0]?
    | pure { status := .failure, message? := some "factor expects exactly one input artifact" }
  let .ok n := StoredArtifact.decodePayload? (α := Nat) target
    | pure { status := .failure, message? := some "factor expects a Nat-valued input artifact" }
  let factorsWithPowers ← session.server.factorNat n
  let mut produced : Array StoredArtifact := #[]
  let mut factorRefs : Array ArtifactRef := #[]
  for (prime, exp) in factorsWithPowers do
    for _ in [:exp] do
      let factorArtifact ← session.mkStoredArtifact "factor" .scalar prime "factor"
      produced := produced.push factorArtifact
      factorRefs := factorRefs.push factorArtifact.ref
  let judgment := Judgment.factorization target.ref factorRefs
  let certificate := Certificate.factorizationWitness target.ref factorRefs
  pure {
    status := .success
    artifacts := produced
    judgments := #[judgment]
    certificates := #[certificate]
    provenance? := some <| macaulay2Provenance "factor"
  }

def Macaulay2Session.quotientRemainderTask (session : Macaulay2Session)
    (request : ResolvedTaskRequest) : IO TaskResult := do
  let some poly := request.inputs[0]?
    | pure { status := .failure, message? := some "quotientRemainder expects a polynomial artifact and an ideal artifact" }
  let some ideal := request.inputs[1]?
    | pure { status := .failure, message? := some "quotientRemainder expects a polynomial artifact and an ideal artifact" }
  let .ok polyData := StoredArtifact.decodePayload? (α := MRDI.Poly) poly
    | pure { status := .failure, message? := some "quotientRemainder expects a polynomial payload" }
  let .ok idealData := StoredArtifact.decodePayload? (α := MRDI.Ideal) ideal
    | pure { status := .failure, message? := some "quotientRemainder expects an ideal payload" }
  let response ← session.server.quotientRemainderPolyData idealData.numVars polyData.data idealData.generators
  if !response.ok then
    return {
      status := .failure
      provenance? := some <| macaulay2Provenance "quotientRemainder"
      message? := some response.status
    }
  let mut quotientArtifacts : Array StoredArtifact := #[]
  let mut quotientRefs : Array ArtifactRef := #[]
  for quotient in response.quotients do
    let qRef ← session.freshRef "quotient"
    let qArtifact : StoredArtifact := {
      ref := qRef
      artifact := Artifact.ofValue .polynomial ({ data := quotient } : MRDI.Poly)
        (some <| macaulay2Provenance "quotientRemainder")
    }
    quotientArtifacts := quotientArtifacts.push qArtifact
    quotientRefs := quotientRefs.push qRef
  let rRef ← session.freshRef "remainder"
  let provenance := macaulay2Provenance "quotientRemainder"
  let rArtifact : StoredArtifact := {
    ref := rRef
    artifact := Artifact.ofValue .polynomial ({ data := response.remainder } : MRDI.Poly) (some provenance)
  }
  let judgment := Judgment.quotientRemainder poly.ref ideal.ref quotientRefs rRef
  let certificate := Certificate.quotientRemainderWitness poly.ref ideal.ref quotientRefs rRef
  pure {
    status := .success
    artifacts := quotientArtifacts.push rArtifact
    judgments := #[judgment]
    certificates := #[certificate]
    provenance? := some provenance
  }

def Macaulay2Session.sumOfSquaresTask (session : Macaulay2Session)
    (request : ResolvedTaskRequest) : IO TaskResult := do
  let some target := request.inputs[0]?
    | pure { status := .failure, message? := some "sumOfSquares expects exactly one polynomial artifact" }
  let .ok polyData := StoredArtifact.decodePayload? (α := MRDI.Poly) target
    | pure { status := .failure, message? := some "sumOfSquares expects a polynomial payload" }
  let numVars := numVarsOfPolynomialData polyData.data
  let response ← session.server.sosCertificateData numVars polyData.data
  if !response.ok then
    return {
      status := .failure
      provenance? := some <| macaulay2Provenance "sumOfSquares"
      message? := some response.status
    }
  if response.scale == 0 then
    return {
      status := .failure
      provenance? := some <| macaulay2Provenance "sumOfSquares"
      message? := some "sumOfSquares returned an invalid zero scale"
    }
  let scaleArtifact ← session.mkStoredArtifact "sosScale" .scalar response.scale "sumOfSquares"
  let mut produced : Array StoredArtifact := #[scaleArtifact]
  let mut summandRefs : Array ArtifactRef := #[]
  for summand in response.summands do
    let summandArtifact ← session.mkStoredArtifact "sosSummand" .sumOfSquaresSummand
      ({ weight := summand.weight, poly := { data := summand.poly } } : SumOfSquaresSummand) "sumOfSquares"
    produced := produced.push summandArtifact
    summandRefs := summandRefs.push summandArtifact.ref
  let judgment := Judgment.sumOfSquares target.ref scaleArtifact.ref summandRefs
  let certificate := Certificate.sumOfSquaresWitness target.ref scaleArtifact.ref summandRefs
  pure {
    status := .success
    artifacts := produced
    judgments := #[judgment]
    certificates := #[certificate]
    provenance? := some <| macaulay2Provenance "sumOfSquares"
  }

instance : BackendSession Macaulay2Session where
  name _ := "Macaulay2"
  capabilities _ := pure #[
    { task := .factor
      exact := true
      certificateBearing := true
      deterministic := true
      inputKinds := #[.scalar]
      outputKinds := #[.scalar] },
    { task := .quotientRemainder
      exact := true
      certificateBearing := true
      deterministic := true
      inputKinds := #[.polynomial, .ideal]
      outputKinds := #[.polynomial, .polynomial] },
    { task := .sumOfSquares
      exact := true
      certificateBearing := true
      deterministic := true
      inputKinds := #[.polynomial]
      outputKinds := #[.scalar, .sumOfSquaresSummand] }
  ]
  runTask session request := do
    match request.task with
    | .factor => session.factorTask request
    | .quotientRemainder => session.quotientRemainderTask request
    | .sumOfSquares => session.sumOfSquaresTask request
    | other =>
        pure {
          status := .unsupported
          provenance? := some <| macaulay2Provenance "unsupported"
          message? := some s!"Macaulay2 backend does not support task {reprStr other}"
        }

private def countFactors (factors : List Nat) : List (Nat × Nat) :=
  let reversed :=
    factors.foldl (init := ([] : List (Nat × Nat))) fun acc factor =>
      match acc with
      | (prev, count) :: rest =>
          if prev == factor then
            (prev, count + 1) :: rest
          else
            (factor, 1) :: acc
      | [] =>
          [(factor, 1)]
  reversed.reverse

def factorNatUsingBackend (session : Macaulay2Session) (n : Nat) : IO (List (Nat × Nat)) := do
  let input : StoredArtifact := {
    ref := { id := s!"input:nat:{n}" }
    artifact := Artifact.ofValue .scalar n
  }
  let initialState := ChainState.recordArtifacts {} #[input]
  let step : ChainStep := {
    backend := "Macaulay2"
    request := {
      task := TaskKind.factor
      inputs := #[input.ref]
    }
    checker? := some { name := "factorization" }
  }
  let outcome ← executeStep session initialState step
  let state ←
    match outcome with
    | Except.ok state => pure state
    | .error err => throw <| IO.userError err
  if state.checkedJudgments.isEmpty then
    throw <| IO.userError "factor step did not produce a checked judgment"
  let factorRefs ←
    match state.checkedJudgments[0]? with
    | some (Judgment.factorization _ factorRefs) => pure factorRefs
    | _ => throw <| IO.userError "factor step did not produce a checked factorization judgment"
  let repeatedFactors ←
    match state.artifacts.resolveInputs? factorRefs with
    | Except.ok artifacts => pure artifacts
    | .error err => throw <| IO.userError err
  let repeatedFactors ← repeatedFactors.toList.mapM fun artifact =>
    match StoredArtifact.decodePayload? (α := Nat) artifact with
    | .ok factor => pure factor
    | .error err => throw <| IO.userError err
  pure <| countFactors repeatedFactors

def quotientRemainderUsingBackend (session : Macaulay2Session) (polyData : MRDI.Poly)
    (idealData : MRDI.Ideal) : IO CheckedQuotientRemainder := do
  let polyInput : StoredArtifact := {
    ref := { id := "input:poly" }
    artifact := Artifact.ofValue .polynomial polyData
  }
  let idealInput : StoredArtifact := {
    ref := { id := "input:ideal" }
    artifact := Artifact.ofValue .ideal idealData
  }
  let initialState := ChainState.recordArtifacts {} #[polyInput, idealInput]
  let step : ChainStep := {
    backend := "Macaulay2"
    request := {
      task := TaskKind.quotientRemainder
      inputs := #[polyInput.ref, idealInput.ref]
    }
    checker? := some { name := "quotientRemainder" }
    discharger? := some { name := "zeroRemainderIdealMembership" }
  }
  let outcome ← executeStep session initialState step
  let state ←
    match outcome with
    | .ok state => pure state
    | .error err => throw <| IO.userError err
  let some qrJudgment := state.checkedJudgments.find? fun judgment =>
      match judgment with
      | .quotientRemainder element ideal _ _ =>
          element == polyInput.ref && ideal == idealInput.ref
      | _ => false
    | throw <| IO.userError "quotient-remainder step did not produce a checked quotient-remainder judgment"
  let (.quotientRemainder _ _ quotientRefs remainderRef) := qrJudgment
    | throw <| IO.userError "unexpected non-quotient-remainder judgment"
  let quotientArtifacts ←
    match state.artifacts.resolveInputs? quotientRefs with
    | .ok artifacts => pure artifacts
    | .error err => throw <| IO.userError err
  let quotients ← quotientArtifacts.toList.mapM fun artifact =>
    match StoredArtifact.decodePayload? (α := MRDI.Poly) artifact with
    | .ok quotient => pure quotient
    | .error err => throw <| IO.userError err
  let remainderArtifact ←
    match state.getArtifact? remainderRef with
    | .ok artifact => pure artifact
    | .error err => throw <| IO.userError err
  let remainder ←
    match StoredArtifact.decodePayload? (α := MRDI.Poly) remainderArtifact with
    | .ok remainder => pure remainder
    | .error err => throw <| IO.userError err
  let idealMembershipJudgment? := state.derivedJudgments.find? fun judgment =>
    judgment == Judgment.idealMembership polyInput.ref idealInput.ref
  pure {
    quotients := quotients.toArray
    remainder := remainder
    quotientRemainderJudgment := qrJudgment
    idealMembershipJudgment? := idealMembershipJudgment?
  }

def idealMembershipUsingBackend (session : Macaulay2Session) (polyData : MRDI.Poly)
    (idealData : MRDI.Ideal) : IO Bool := do
  return (← quotientRemainderUsingBackend session polyData idealData).idealMembershipJudgment?.isSome

def sumOfSquaresUsingBackend (session : Macaulay2Session) (polyData : MRDI.Poly) :
    IO CheckedSumOfSquares := do
  let polyInput : StoredArtifact := {
    ref := { id := "input:sos:poly" }
    artifact := Artifact.ofValue .polynomial polyData
  }
  let initialState := ChainState.recordArtifacts {} #[polyInput]
  let step : ChainStep := {
    backend := "Macaulay2"
    request := {
      task := TaskKind.sumOfSquares
      inputs := #[polyInput.ref]
    }
    checker? := some { name := "sumOfSquares" }
    discharger? := some { name := "sumOfSquaresNonnegativity" }
  }
  let outcome ← executeStep session initialState step
  let state ←
    match outcome with
    | .ok state => pure state
    | .error err => throw <| IO.userError err
  let some sosJudgment := state.checkedJudgments.find? fun judgment =>
      match judgment with
      | .sumOfSquares target _ _ => target == polyInput.ref
      | _ => false
    | throw <| IO.userError "sum-of-squares step did not produce a checked SOS judgment"
  let (.sumOfSquares _ scaleRef summandRefs) := sosJudgment
    | throw <| IO.userError "unexpected non-SOS judgment"
  let scaleArtifact ←
    match state.getArtifact? scaleRef with
    | .ok artifact => pure artifact
    | .error err => throw <| IO.userError err
  let scale ←
    match StoredArtifact.decodePayload? (α := Nat) scaleArtifact with
    | .ok scale => pure scale
    | .error err => throw <| IO.userError err
  let summandArtifacts ←
    match state.artifacts.resolveInputs? summandRefs with
    | .ok artifacts => pure artifacts
    | .error err => throw <| IO.userError err
  let summands ← summandArtifacts.toList.mapM fun artifact =>
    match StoredArtifact.decodePayload? (α := SumOfSquaresSummand) artifact with
    | .ok summand => pure summand
    | .error err => throw <| IO.userError err
  let nonnegativityJudgment? := state.derivedJudgments.find? fun judgment =>
    judgment == Judgment.nonnegativity polyInput.ref
  pure {
    scale := scale
    summands := summands.toArray
    sumOfSquaresJudgment := sosJudgment
    nonnegativityJudgment? := nonnegativityJudgment?
  }

def macaulay2Backend : BackendFactory where
  Session := Macaulay2Session
  start := Macaulay2Session.start
  stop := Macaulay2Session.stop

end Macaulean.CAS
