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

/-! # SymPy Backend

Registers SymPy as a CAS backend via a long-lived Python JSON-RPC server.
Proves the backend abstraction works with a non-M2 backend.
-/

structure SymPySessionState where
  nextRequestId : IO.Ref Nat

def SymPySessionState.new : IO SymPySessionState := do
  let nextRequestId ← IO.mkRef 1
  pure { nextRequestId }

def sendSymPyRequest [ToJson α] [FromJson β] (streams : CAS.BackendStreams)
    (state : SymPySessionState) (method : String) (body : α) : IO β := do
  let reqId ← JsonRpc.RequestID.num <$>
    state.nextRequestId.modifyGet (fun x => (x, x + 1))
  streams.stdin.writeLspRequest { id := reqId, method := method, param := body }
  let response ← streams.stdout.readLspResponseAs reqId (α := β)
  pure response.result

-- ============================================================================
-- Request translation: MRDI -> SymPy JSON-RPC -> MRDI
-- ============================================================================

structure SymPyQRRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure SymPyQRResponse where
  ok : Bool
  status : String
  quotients : Array MRDI.PolynomialData
  remainder : MRDI.PolynomialData
  deriving ToJson, FromJson

structure SymPyGBRequest where
  numVars : Nat
  generators : Array MRDI.PolynomialData
  order : String
  deriving ToJson, FromJson

structure SymPyGBResponse where
  generators : Array MRDI.PolynomialData
  deriving ToJson, FromJson

def handleSymPyReduction (streams : CAS.BackendStreams) (state : SymPySessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := ReductionProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode ReductionProblem: {e}"
  let m2Req : SymPyQRRequest := {
    numVars := problem.ideal.ring.vars.size
    polyData := problem.element.data
    idealData := problem.ideal.generators
  }
  let resp ← sendSymPyRequest streams state "quotientRemainderPolyData" m2Req
    (β := SymPyQRResponse)
  if !resp.ok then
    return .failure s!"SymPy quotientRemainder failed: {resp.status}"
  let result : ReductionResult := {
    method := "sympy_reduced"
    quotients := resp.quotients
    remainder := resp.remainder
  }
  pure (.ok (toMrdi result))

def handleSymPyFactorization (streams : CAS.BackendStreams) (state : SymPySessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := FactorizationProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode FactorizationProblem: {e}"
  let response : List (List Nat) ← sendSymPyRequest streams state "factorInt" [problem.n]
  let factors := response.toArray.map fun p =>
    match p with
    | [a, b] => (a, b)
    | _ => (1, 1)
  let result : FactorizationResult := { factors }
  pure (.ok (toMrdi result))

def handleSymPyGroebner (streams : CAS.BackendStreams) (state : SymPySessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := GroebnerBasisProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode GroebnerBasisProblem: {e}"
  let orderStr := match problem.order with
    | .lex => "lex" | .grlex => "grlex" | .grevlex => "grevlex" | .named s => s
  let gbReq : SymPyGBRequest := {
    numVars := problem.ring.vars.size
    generators := problem.generators
    order := orderStr
  }
  let resp ← sendSymPyRequest streams state "groebnerBasis" gbReq
    (β := SymPyGBResponse)
  let result : GroebnerBasisResult := { generators := resp.generators }
  pure (.ok (toMrdi result))

-- ============================================================================
-- Polynomial factorization
-- ============================================================================

structure SymPyPolyFactorRequest where
  numVars : Nat
  polynomial : MRDI.PolynomialData
  deriving ToJson, FromJson

structure SymPyPolyFactorResponse where
  factors : Array MRDI.PolynomialData
  deriving ToJson, FromJson

def handleSymPyPolyFactorization (streams : CAS.BackendStreams) (state : SymPySessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := PolyFactorizationProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode PolyFactorizationProblem: {e}"
  let req : SymPyPolyFactorRequest := {
    numVars := problem.ring.vars.size
    polynomial := problem.polynomial
  }
  let resp ← sendSymPyRequest streams state "polyFactorization" req
    (β := SymPyPolyFactorResponse)
  let result : PolyFactorizationResult := { factors := resp.factors }
  pure (.ok (toMrdi result))

-- ============================================================================
-- Radical membership
-- ============================================================================

structure SymPyRadicalRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure SymPyRadicalResponse where
  inRadical : Bool
  power : Nat
  quotients : Array MRDI.PolynomialData
  deriving ToJson, FromJson

def handleSymPyRadicalMembership (streams : CAS.BackendStreams) (state : SymPySessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := RadicalMembershipProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode RadicalMembershipProblem: {e}"
  let req : SymPyRadicalRequest := {
    numVars := problem.ideal.ring.vars.size
    polyData := problem.element.data
    idealData := problem.ideal.generators
  }
  let resp ← sendSymPyRequest streams state "radicalMembership" req
    (β := SymPyRadicalResponse)
  if !resp.inRadical then
    return .failure "Element is not in the radical of the ideal"
  let result : RadicalMembershipResult := {
    power := resp.power
    quotients := resp.quotients
  }
  pure (.ok (toMrdi result))

-- ============================================================================
-- Backend Registration
-- ============================================================================

initialize do
  let stateRef ← IO.mkRef (none : Option SymPySessionState)
  CAS.registerCASBackend {
    name := `SymPy
    priority := 2000  -- lower priority than M2 (1000), used as fallback
    cmd := "python3"
    args := #["./sympy/macaulean_sympy.py"]
    requestTimeout := 30000
    supports := fun type =>
      type == .string "reduction_problem" ||
      type == .string "factorization_problem" ||
      type == .string "groebner_basis_problem" ||
      type == .string "radical_membership_problem" ||
      type == .string "poly_factorization_problem"
    handleRequest := fun streams request => do
      let state ← match ← stateRef.get with
        | some s => pure s
        | none =>
            let s ← SymPySessionState.new
            stateRef.set (some s)
            pure s
      match request.type with
      | .string "reduction_problem" =>
          handleSymPyReduction streams state request
      | .string "factorization_problem" =>
          handleSymPyFactorization streams state request
      | .string "groebner_basis_problem" =>
          handleSymPyGroebner streams state request
      | .string "radical_membership_problem" =>
          handleSymPyRadicalMembership streams state request
      | .string "poly_factorization_problem" =>
          handleSymPyPolyFactorization streams state request
      | _ => pure (.unsupported s!"SymPy does not support: {toJson request.type}")
  }

end Macaulean
