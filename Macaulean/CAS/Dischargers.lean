import Macaulean.CAS.Checkers
import Macaulean.Serialize
import MRDI.Poly

namespace Macaulean.CAS

structure JudgmentDischarger where
  name : DischargerName
  discharge : ChainState → Array Judgment → Except String (Array Judgment)

private def isZeroPolynomialData (polyData : MRDI.PolynomialData) : Bool :=
  Lean.Grind.CommRing.PolynomialData.deserialize polyData == .num 0

def dischargeZeroRemainderIdealMembership (state : ChainState) (judgments : Array Judgment) :
    Except String (Array Judgment) := do
  let mut derived := #[]
  for judgment in judgments do
    match judgment with
    | .quotientRemainder element ideal _ remainderRef =>
        let remainderArtifact ← state.getArtifact? remainderRef
        let remainderPoly ← remainderArtifact.decodePayload? (α := MRDI.Poly)
        if isZeroPolynomialData remainderPoly.data then
          derived := derived.push <| Judgment.idealMembership element ideal
    | _ =>
        pure ()
  pure derived

def dischargeSumOfSquaresNonnegativity (_state : ChainState) (judgments : Array Judgment) :
    Except String (Array Judgment) := do
  let mut derived := #[]
  for judgment in judgments do
    match judgment with
    | .sumOfSquares target _ _ =>
        derived := derived.push <| Judgment.nonnegativity target
    | _ =>
        pure ()
  pure derived

def zeroRemainderIdealMembershipDischarger : JudgmentDischarger :=
  { name := { name := "zeroRemainderIdealMembership" }
    discharge := dischargeZeroRemainderIdealMembership }

def sumOfSquaresNonnegativityDischarger : JudgmentDischarger :=
  { name := { name := "sumOfSquaresNonnegativity" }
    discharge := dischargeSumOfSquaresNonnegativity }

def builtinJudgmentDischargers : Array JudgmentDischarger :=
  #[zeroRemainderIdealMembershipDischarger, sumOfSquaresNonnegativityDischarger]

def findJudgmentDischarger? (name : DischargerName) : Option JudgmentDischarger :=
  builtinJudgmentDischargers.find? fun discharger => discharger.name == name

end Macaulean.CAS
