import Macaulean.CAS
import Macaulean.Serialize

open Lean.Grind.CommRing

open Lean Json
open Macaulean.CAS

namespace MacauleanTest.CASBackend

def requireIO (cond : Bool) (msg : String) : IO Unit :=
  unless cond do
    throw <| IO.userError msg

def factorInput : StoredArtifact :=
  { ref := { id := "input:nat:12" }
    artifact := Artifact.ofValue .scalar (12 : Nat) }

def x : Expr := .var 0
def y : Expr := .var 1

instance : Add Expr where
  add a b := .add a b
instance : Sub Expr where
  sub a b := .sub a b
instance : Neg Expr where
  neg a := .neg a
instance : Mul Expr where
  mul a b := .mul a b
instance : HPow Expr Nat Expr where
  hPow a k := .pow a k
instance : OfNat Expr n where
  ofNat := .num n

def qrPoly : MRDI.Poly := { data := (x^3).toPoly.serialize }
def qrMemberPoly : MRDI.Poly := { data := (x^3 - x*y).toPoly.serialize }
def sosPoly : MRDI.Poly := { data := (x^2 + y^2).toPoly.serialize }
def qrIdeal : MRDI.Ideal := {
  numVars := 2
  generators := #[
    (x^2 - y).toPoly.serialize,
    (y^2).toPoly.serialize
  ]
}

def qrPolyInput : StoredArtifact :=
  { ref := { id := "input:poly:x3" }
    artifact := Artifact.ofValue .polynomial qrPoly }

def qrIdealInput : StoredArtifact :=
  { ref := { id := "input:ideal:test" }
    artifact := Artifact.ofValue .ideal qrIdeal }

def qrMemberPolyInput : StoredArtifact :=
  { ref := { id := "input:poly:member" }
    artifact := Artifact.ofValue .polynomial qrMemberPoly }

def decodeNatArtifact (artifact : StoredArtifact) : IO Nat := do
  match StoredArtifact.decodePayload? (α := Nat) artifact with
  | .ok n => pure n
  | .error err => throw <| IO.userError err

#eval do
  let session ← Macaulay2Session.start
  let caps ← BackendSession.capabilities session
  requireIO (caps.any fun cap => cap.task == TaskKind.factor && cap.certificateBearing)
    "Macaulay2 backend should advertise certified factorization"
  requireIO (caps.any fun cap => cap.task == TaskKind.quotientRemainder && cap.certificateBearing)
    "Macaulay2 backend should advertise certified quotient-remainder"
  requireIO (caps.any fun cap => cap.task == TaskKind.sumOfSquares && cap.certificateBearing)
    "Macaulay2 backend should advertise certified SOS"

  let result ← BackendSession.runTask session {
    task := TaskKind.factor
    inputs := #[factorInput]
  }
  requireIO (result.status == TaskStatus.success) "factor task should succeed"
  requireIO (result.artifacts.size == 3) "factor task should return three prime factors for 12"

  let factors ← result.artifacts.toList.mapM decodeNatArtifact
  requireIO (factors == [2, 2, 3]) s!"unexpected factorization payloads: {factors}"

  let some cert := result.certificates[0]?
    | throw <| IO.userError "factor task should return a certificate"
  match cert with
  | Certificate.factorizationWitness target factors =>
      requireIO (target == factorInput.ref) "factorization certificate should point to the input artifact"
      requireIO (factors == result.artifacts.map (fun (artifact : StoredArtifact) => artifact.ref))
        "factorization certificate should point to produced factor artifacts"
  | _ =>
      throw <| IO.userError "factor task returned the wrong certificate shape"

  let sosResult ← BackendSession.runTask session {
    task := TaskKind.sumOfSquares
    inputs := #[{
      ref := { id := "input:sos" }
      artifact := Artifact.ofValue .polynomial sosPoly
    }]
  }
  requireIO (sosResult.status == TaskStatus.success) "SOS task should succeed on x^2 + y^2"
  requireIO (sosResult.artifacts.size >= 2) "SOS task should return a scale and at least one summand"

  let executed ← executeStep session (ChainState.recordArtifacts {} #[factorInput]) {
    backend := "Macaulay2"
    request := {
      task := TaskKind.factor
      inputs := #[factorInput.ref]
    }
    checker? := some { name := "factorization" }
  }
  let state ←
    match executed with
    | .ok state => pure state
    | .error err => throw <| IO.userError err
  requireIO (state.checkedJudgments.size == 1) "executeStep should record one checked factorization judgment"

  let qrResult ← BackendSession.runTask session {
    task := TaskKind.quotientRemainder
    inputs := #[qrPolyInput, qrIdealInput]
  }
  requireIO (qrResult.status == TaskStatus.success) "quotient-remainder task should succeed"
  requireIO (qrResult.artifacts.size == 3) "quotient-remainder should return two quotients and one remainder"

  let executedQr ← executeStep session (ChainState.recordArtifacts {} #[qrPolyInput, qrIdealInput]) {
    backend := "Macaulay2"
    request := {
      task := TaskKind.quotientRemainder
      inputs := #[qrPolyInput.ref, qrIdealInput.ref]
    }
    checker? := some { name := "quotientRemainder" }
  }
  let qrState ←
    match executedQr with
    | .ok state => pure state
    | .error err => throw <| IO.userError err
  requireIO (qrState.checkedJudgments.size == 1)
    "executeStep should record one checked quotient-remainder judgment"

  let executedMemberQr ← executeStep session (ChainState.recordArtifacts {} #[qrMemberPolyInput, qrIdealInput]) {
    backend := "Macaulay2"
    request := {
      task := TaskKind.quotientRemainder
      inputs := #[qrMemberPolyInput.ref, qrIdealInput.ref]
    }
    checker? := some { name := "quotientRemainder" }
    discharger? := some { name := "zeroRemainderIdealMembership" }
  }
  let memberState ←
    match executedMemberQr with
    | .ok state => pure state
    | .error err => throw <| IO.userError err
  requireIO (memberState.derivedJudgments ==
      #[Judgment.idealMembership qrMemberPolyInput.ref qrIdealInput.ref])
    "zero-remainder discharger should derive ideal membership"

  let qrWitness ← quotientRemainderUsingBackend session qrMemberPoly qrIdeal
  requireIO (qrWitness.quotients.size == 2)
    "quotientRemainderUsingBackend should expose both quotient artifacts"
  requireIO (qrWitness.idealMembershipJudgment?.isSome)
    "quotientRemainderUsingBackend should surface derived ideal membership"

  let isMember ← idealMembershipUsingBackend session qrMemberPoly qrIdeal
  requireIO isMember "idealMembershipUsingBackend should report a zero-remainder member"

  let isNotMember ← idealMembershipUsingBackend session qrPoly qrIdeal
  requireIO (!isNotMember) "idealMembershipUsingBackend should reject non-members"

  let sosWitness ← sumOfSquaresUsingBackend session sosPoly
  requireIO (sosWitness.scale > 0) "sumOfSquaresUsingBackend should return a positive scale"
  requireIO (!sosWitness.summands.isEmpty) "sumOfSquaresUsingBackend should return at least one summand"
  requireIO (sosWitness.nonnegativityJudgment?.isSome)
    "sumOfSquaresUsingBackend should surface derived nonnegativity"

end MacauleanTest.CASBackend
