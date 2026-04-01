import Lean.Data.JsonRpc
import Lean.Data.Json
import Lean.Data.Lsp.Communication
import MRDI.Basic
import MRDI.Poly
import MRDI.CAS
import Macaulean.CAS.Backend

open Lean Json
open MRDI.CAS

namespace Macaulean

/-! # Macaulay2 Backend

Registers Macaulay2 as a CAS backend. The framework manages the process;
this file only provides the request translator.
-/

-- ============================================================================
-- LSP/JSON-RPC communication over BackendStreams
-- ============================================================================

/-- Per-session request counter for JSON-RPC IDs. -/
structure M2SessionState where
  nextRequestId : IO.Ref Nat

def M2SessionState.new : IO M2SessionState := do
  let nextRequestId ← IO.mkRef 1
  pure { nextRequestId }

def sendM2Request [ToJson α] [FromJson β] (streams : CAS.BackendStreams)
    (state : M2SessionState) (method : String) (body : α) : IO β := do
  let reqId ← JsonRpc.RequestID.num <$>
    state.nextRequestId.modifyGet (fun x => (x, x + 1))
  streams.stdin.writeLspRequest { id := reqId, method := method, param := body }
  let response ← streams.stdout.readLspResponseAs reqId (α := β)
  pure response.result

-- ============================================================================
-- M2 request/response types (kept from original, used by handleRequest)
-- ============================================================================

structure QuotientRemainderPolyRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving Repr, ToJson, FromJson

structure QuotientRemainderPolyResponse where
  ok : Bool
  status : String
  quotients : Array MRDI.PolynomialData
  remainder : MRDI.PolynomialData
  deriving Repr, ToJson, FromJson

-- ============================================================================
-- Request translation: MRDI -> M2 JSON-RPC -> MRDI
-- ============================================================================

/-- Translate a ReductionProblem MRDI into M2's quotientRemainderPolyData call. -/
def handleReductionProblem (streams : CAS.BackendStreams) (state : M2SessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := ReductionProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode ReductionProblem: {e}"
  let m2Req : QuotientRemainderPolyRequest := {
    numVars := problem.ideal.ring.vars.size
    polyData := problem.element.data
    idealData := problem.ideal.generators
  }
  let resp ← sendM2Request streams state "quotientRemainderPolyData" m2Req
    (β := QuotientRemainderPolyResponse)
  if !resp.ok then
    return .failure s!"M2 quotientRemainder failed: {resp.status}"
  let result : ReductionResult := {
    method := "groebner_basis"
    quotients := resp.quotients
    remainder := resp.remainder
  }
  pure (.ok (toMrdi result))

/-- Translate a FactorizationProblem MRDI into M2's factorInt call. -/
def handleFactorizationProblem (streams : CAS.BackendStreams) (state : M2SessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := FactorizationProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode FactorizationProblem: {e}"
  let response : List (List Nat) ← sendM2Request streams state "factorInt" [problem.n]
  let factors := response.toArray.map fun p =>
    match p with
    | [a, b] => (a, b)
    | _ => (1, 1)
  let result : FactorizationResult := { factors }
  pure (.ok (toMrdi result))

-- ============================================================================
-- Radical membership
-- ============================================================================

structure M2RadicalRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure M2RadicalResponse where
  inRadical : Bool
  power : Nat
  quotients : Array MRDI.PolynomialData
  deriving ToJson, FromJson

def handleRadicalMembership (streams : CAS.BackendStreams) (state : M2SessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := RadicalMembershipProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode RadicalMembershipProblem: {e}"
  let req : M2RadicalRequest := {
    numVars := problem.ideal.ring.vars.size
    polyData := problem.element.data
    idealData := problem.ideal.generators
  }
  let resp ← sendM2Request streams state "radicalMembership" req (β := M2RadicalResponse)
  if !resp.inRadical then
    return .failure "Element is not in the radical of the ideal"
  let result : RadicalMembershipResult := {
    power := resp.power
    quotients := resp.quotients
  }
  pure (.ok (toMrdi result))

-- ============================================================================
-- Gröbner basis
-- ============================================================================

structure M2GBRequest where
  numVars : Nat
  generators : Array MRDI.PolynomialData
  order : String
  deriving ToJson, FromJson

structure M2GBResponse where
  generators : Array MRDI.PolynomialData
  deriving ToJson, FromJson

def handleGroebnerBasis (streams : CAS.BackendStreams) (state : M2SessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := GroebnerBasisProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode GroebnerBasisProblem: {e}"
  let orderStr := match problem.order with
    | .lex => "lex" | .grlex => "grlex" | .grevlex => "grevlex" | .named s => s
  let gbReq : M2GBRequest := {
    numVars := problem.ring.vars.size
    generators := problem.generators
    order := orderStr
  }
  let resp ← sendM2Request streams state "groebnerBasis" gbReq (β := M2GBResponse)
  let result : GroebnerBasisResult := { generators := resp.generators }
  pure (.ok (toMrdi result))

-- ============================================================================
-- Backend Registration
-- ============================================================================

/-- Per-session state, created when the backend session starts.
Stored via closure in handleRequest. -/
initialize do
  let stateRef ← IO.mkRef (none : Option M2SessionState)
  CAS.registerCASBackend {
    name := `Macaulay2
    priority := 1000
    cmd := "M2"
    args := #["--script", "./macaulean.m2"]
    cwd := some "./m2/"
    requestTimeout := 30000
    supports := fun type =>
      type == .string "reduction_problem" ||
      type == .string "factorization_problem" ||
      type == .string "groebner_basis_problem" ||
      type == .string "radical_membership_problem"
    handleRequest := fun streams request => do
      -- Lazy init of per-session state (request counter)
      let state ← match ← stateRef.get with
        | some s => pure s
        | none =>
            let s ← M2SessionState.new
            stateRef.set (some s)
            pure s
      match request.type with
      | .string "reduction_problem" =>
          handleReductionProblem streams state request
      | .string "factorization_problem" =>
          handleFactorizationProblem streams state request
      | .string "groebner_basis_problem" =>
          handleGroebnerBasis streams state request
      | .string "radical_membership_problem" =>
          handleRadicalMembership streams state request
      | _ => pure (.unsupported s!"Macaulay2 does not support: {toJson request.type}")
  }

end Macaulean
