import MRDI.Basic

open Lean Json

namespace Macaulean.CAS

abbrev ArtifactId := Uuid

structure ArtifactRef where
  id : ArtifactId
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive BaseDomain where
  | nat
  | int
  | rat
  | primeField (p : Nat)
  | named (name : String) (params : Json := .null)
  deriving BEq, ToJson, FromJson

inductive MonomialOrder where
  | lex
  | grlex
  | grevlex
  | named (name : String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure PolynomialRingContext where
  coeffDomain : ArtifactRef
  variables : Array String
  order : MonomialOrder := .grevlex
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

inductive ArtifactKind where
  | scalar
  | ring
  | polynomialRing
  | polynomial
  | ideal
  | matrix
  | module
  | judgment
  | certificate
  | backendSpecific (name : String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure Provenance where
  backend : String
  version? : Option String := none
  task : String
  deterministic : Bool := true
  options : Json := .null
  deriving BEq, ToJson, FromJson

inductive Judgment where
  | equality (lhs rhs : ArtifactRef)
  | idealMembership (element ideal : ArtifactRef)
  | quotientRemainder
      (element : ArtifactRef)
      (ideal : ArtifactRef)
      (quotients : Array ArtifactRef)
      (remainder : ArtifactRef)
  | factorization (target : ArtifactRef) (factors : Array ArtifactRef)
  | nonnegativity (target : ArtifactRef)
  | backendSpecific (name : String) (payload : Json := .null)
  deriving BEq, ToJson, FromJson

inductive Certificate where
  | equalityWitness (judgment : Judgment) (witness : ArtifactRef)
  | quotientRemainderWitness
      (element : ArtifactRef)
      (ideal : ArtifactRef)
      (quotients : Array ArtifactRef)
      (remainder : ArtifactRef)
  | factorizationWitness (target : ArtifactRef) (factors : Array ArtifactRef)
  | sumOfSquaresWitness
      (target : ArtifactRef)
      (scale : ArtifactRef)
      (summands : Array ArtifactRef)
  | backendSpecific (name : String) (payload : Json := .null)
  deriving BEq, ToJson, FromJson

structure Artifact where
  kind : ArtifactKind
  payload : Mrdi
  provenance? : Option Provenance := none
  deriving ToJson, FromJson

structure StoredArtifact where
  ref : ArtifactRef
  artifact : Artifact
  deriving ToJson, FromJson

def Artifact.ofValue [MrdiType α] (kind : ArtifactKind) (value : α)
    (provenance? : Option Provenance := none) : Artifact :=
  { kind := kind, payload := toMrdi value, provenance? := provenance? }

def StoredArtifact.decodePayload? [MrdiType α] (artifact : StoredArtifact) : Except String α :=
  fromMrdi? artifact.artifact.payload

instance : MrdiType ArtifactRef where
  mrdiType := .string "Macaulean.CAS.ArtifactRef"
  decode? := trivialDecode? (.string "Macaulean.CAS.ArtifactRef")

instance : MrdiType BaseDomain where
  mrdiType := .string "Macaulean.CAS.BaseDomain"
  decode? := trivialDecode? (.string "Macaulean.CAS.BaseDomain")

instance : MrdiType MonomialOrder where
  mrdiType := .string "Macaulean.CAS.MonomialOrder"
  decode? := trivialDecode? (.string "Macaulean.CAS.MonomialOrder")

instance : MrdiType PolynomialRingContext where
  mrdiType := .string "Macaulean.CAS.PolynomialRingContext"
  decode? := trivialDecode? (.string "Macaulean.CAS.PolynomialRingContext")

instance : MrdiType ArtifactKind where
  mrdiType := .string "Macaulean.CAS.ArtifactKind"
  decode? := trivialDecode? (.string "Macaulean.CAS.ArtifactKind")

instance : MrdiType Provenance where
  mrdiType := .string "Macaulean.CAS.Provenance"
  decode? := trivialDecode? (.string "Macaulean.CAS.Provenance")

instance : MrdiType Judgment where
  mrdiType := .string "Macaulean.CAS.Judgment"
  decode? := trivialDecode? (.string "Macaulean.CAS.Judgment")

instance : MrdiType Certificate where
  mrdiType := .string "Macaulean.CAS.Certificate"
  decode? := trivialDecode? (.string "Macaulean.CAS.Certificate")

instance : MrdiType Artifact where
  mrdiType := .string "Macaulean.CAS.Artifact"
  decode? := trivialDecode? (.string "Macaulean.CAS.Artifact")

instance : MrdiType StoredArtifact where
  mrdiType := .string "Macaulean.CAS.StoredArtifact"
  decode? := trivialDecode? (.string "Macaulean.CAS.StoredArtifact")

end Macaulean.CAS
