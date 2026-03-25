import Macaulean.CAS.Chain
import Macaulean.Serialize
import MRDI.Poly

namespace Macaulean.CAS

structure CertificateChecker where
  name : CheckerName
  check : ChainState → Certificate → Except String Judgment

def ChainState.getArtifact? (state : ChainState) (ref : ArtifactRef) : Except String StoredArtifact := do
  let some artifact := state.artifacts.find? ref
    | .error s!"Unknown artifact ref: {ref.id}"
  pure artifact

private def natProduct (factors : List Nat) : Nat :=
  factors.foldl (· * ·) 1

def checkFactorizationCertificate (state : ChainState) (certificate : Certificate) :
    Except String Judgment := do
  match certificate with
  | .factorizationWitness target factorRefs =>
      let targetArtifact ← state.getArtifact? target
      let targetNat ← targetArtifact.decodePayload? (α := Nat)
      let factorArtifacts ← state.artifacts.resolveInputs? factorRefs
      let factors ← factorArtifacts.toList.mapM fun artifact => artifact.decodePayload? (α := Nat)
      if natProduct factors == targetNat then
        pure <| Judgment.factorization target factorRefs
      else
        .error s!"Invalid factorization certificate: product {natProduct factors} does not equal {targetNat}"
  | _ =>
      .error "Certificate is not a factorization witness"

private def combineMany (polys : List Lean.Grind.CommRing.Poly) : Lean.Grind.CommRing.Poly :=
  polys.foldl (init := .num 0) fun acc poly => acc.combine poly

def checkQuotientRemainderCertificate (state : ChainState) (certificate : Certificate) :
    Except String Judgment := do
  match certificate with
  | .quotientRemainderWitness element ideal quotientRefs remainderRef =>
      let elementArtifact ← state.getArtifact? element
      let elementPoly ← elementArtifact.decodePayload? (α := MRDI.Poly)
      let idealArtifact ← state.getArtifact? ideal
      let idealData ← idealArtifact.decodePayload? (α := MRDI.Ideal)
      let quotientArtifacts ← state.artifacts.resolveInputs? quotientRefs
      let quotients ← quotientArtifacts.toList.mapM fun artifact => artifact.decodePayload? (α := MRDI.Poly)
      let remainderArtifact ← state.getArtifact? remainderRef
      let remainderPoly ← remainderArtifact.decodePayload? (α := MRDI.Poly)
      if quotients.length != idealData.generators.size then
        .error "Invalid quotient-remainder certificate: quotient count does not match generator count"
      else
        let lhs := Lean.Grind.CommRing.PolynomialData.deserialize elementPoly.data
        let rhsTerms :=
          List.zipWith
            (fun q g =>
              (Lean.Grind.CommRing.PolynomialData.deserialize q.data).mul
                (Lean.Grind.CommRing.PolynomialData.deserialize g))
            quotients
            idealData.generators.toList
        let rhs := (combineMany rhsTerms).combine
          (Lean.Grind.CommRing.PolynomialData.deserialize remainderPoly.data)
        if lhs == rhs then
          pure <| Judgment.quotientRemainder element ideal quotientRefs remainderRef
        else
          .error "Invalid quotient-remainder certificate: polynomial identity does not hold"
  | _ =>
      .error "Certificate is not a quotient-remainder witness"

def factorizationCertificateChecker : CertificateChecker :=
  { name := { name := "factorization" }
    check := checkFactorizationCertificate }

def quotientRemainderCertificateChecker : CertificateChecker :=
  { name := { name := "quotientRemainder" }
    check := checkQuotientRemainderCertificate }

def builtinCertificateCheckers : Array CertificateChecker :=
  #[factorizationCertificateChecker, quotientRemainderCertificateChecker]

def findCertificateChecker? (name : CheckerName) : Option CertificateChecker :=
  builtinCertificateCheckers.find? fun checker => checker.name == name

end Macaulean.CAS
