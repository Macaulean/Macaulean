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

/-! # Oscar Backend

Registers Oscar (Julia) as a CAS backend. Third backend alongside M2 and SymPy,
proving the architecture scales to multiple languages and CAS systems.
-/

structure OscarSessionState where
  nextRequestId : IO.Ref Nat

def OscarSessionState.new : IO OscarSessionState := do
  let nextRequestId ← IO.mkRef 1
  pure { nextRequestId }

def sendOscarRequest [ToJson α] [FromJson β] (streams : CAS.BackendStreams)
    (state : OscarSessionState) (method : String) (body : α) : IO β := do
  let reqId ← JsonRpc.RequestID.num <$>
    state.nextRequestId.modifyGet (fun x => (x, x + 1))
  streams.stdin.writeLspRequest { id := reqId, method := method, param := body }
  let response ← streams.stdout.readLspResponseAs reqId (α := β)
  pure response.result

-- ============================================================================
-- Request types (same JSON format as M2/SymPy for interop)
-- ============================================================================

structure OscarQRRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure OscarQRResponse where
  ok : Bool
  status : String
  quotients : Array MRDI.PolynomialData
  remainder : MRDI.PolynomialData
  deriving ToJson, FromJson

structure OscarGBRequest where
  numVars : Nat
  generators : Array MRDI.PolynomialData
  order : String
  deriving ToJson, FromJson

structure OscarGBResponse where
  generators : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure OscarPolyFactorRequest where
  numVars : Nat
  polynomial : MRDI.PolynomialData
  deriving ToJson, FromJson

structure OscarPolyFactorResponse where
  factors : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure OscarRadicalRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving ToJson, FromJson

structure OscarRadicalResponse where
  inRadical : Bool
  power : Nat
  quotients : Array MRDI.PolynomialData
  deriving ToJson, FromJson

-- ============================================================================
-- Request handlers
-- ============================================================================

def handleOscarReduction (streams : CAS.BackendStreams) (state : OscarSessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := ReductionProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode ReductionProblem: {e}"
  let req : OscarQRRequest := {
    numVars := problem.ideal.ring.vars.size
    polyData := problem.element.data
    idealData := problem.ideal.generators
  }
  let resp ← sendOscarRequest streams state "quotientRemainderPolyData" req
    (β := OscarQRResponse)
  if !resp.ok then return .failure s!"Oscar QR failed: {resp.status}"
  pure (.ok (toMrdi ({ method := "oscar_divrem", quotients := resp.quotients, remainder := resp.remainder } : ReductionResult)))

def handleOscarGroebner (streams : CAS.BackendStreams) (state : OscarSessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := GroebnerBasisProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode GroebnerBasisProblem: {e}"
  let orderStr := match problem.order with
    | .lex => "lex" | .grlex => "grlex" | .grevlex => "grevlex" | .named s => s
  let req : OscarGBRequest := { numVars := problem.ring.vars.size, generators := problem.generators, order := orderStr }
  let resp ← sendOscarRequest streams state "groebnerBasis" req (β := OscarGBResponse)
  pure (.ok (toMrdi ({ generators := resp.generators } : GroebnerBasisResult)))

def handleOscarPolyFactor (streams : CAS.BackendStreams) (state : OscarSessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := PolyFactorizationProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode PolyFactorizationProblem: {e}"
  let req : OscarPolyFactorRequest := { numVars := problem.ring.vars.size, polynomial := problem.polynomial }
  let resp ← sendOscarRequest streams state "polyFactorization" req (β := OscarPolyFactorResponse)
  pure (.ok (toMrdi ({ factors := resp.factors } : PolyFactorizationResult)))

def handleOscarFactorInt (streams : CAS.BackendStreams) (state : OscarSessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := FactorizationProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode FactorizationProblem: {e}"
  let response : List (List Nat) ← sendOscarRequest streams state "factorInt" [problem.n]
  let factors := response.toArray.map fun p => match p with | [a, b] => (a, b) | _ => (1, 1)
  pure (.ok (toMrdi ({ factors } : FactorizationResult)))

def handleOscarRadical (streams : CAS.BackendStreams) (state : OscarSessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := RadicalMembershipProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode RadicalMembershipProblem: {e}"
  let req : OscarRadicalRequest := {
    numVars := problem.ideal.ring.vars.size
    polyData := problem.element.data
    idealData := problem.ideal.generators
  }
  let resp ← sendOscarRequest streams state "radicalMembership" req (β := OscarRadicalResponse)
  if !resp.inRadical then return .failure "Element is not in the radical of the ideal"
  pure (.ok (toMrdi ({ power := resp.power, quotients := resp.quotients } : RadicalMembershipResult)))

-- ============================================================================
-- Permutation group membership
-- ============================================================================

structure OscarPermRequest where
  size : Nat
  generators : Array (Array Nat)
  target : Array Nat
  deriving ToJson, FromJson

structure OscarPermResponse where
  inGroup : Bool
  word : Array Int
  deriving ToJson, FromJson

def handleOscarPermGroupMembership (streams : CAS.BackendStreams) (state : OscarSessionState)
    (request : Mrdi) : IO CAS.BackendResult := do
  let problem ← match fromJson? (α := PermGroupMembershipProblem) request.data with
    | .ok p => pure p
    | .error e => return .unsupported s!"Failed to decode PermGroupMembershipProblem: {e}"
  let req : OscarPermRequest := {
    size := problem.size
    generators := problem.generators
    target := problem.target
  }
  let resp ← sendOscarRequest streams state "permGroupMembership" req (β := OscarPermResponse)
  if !resp.inGroup then
    return .failure "Permutation is not in the generated group"
  pure (.ok (toMrdi ({ inGroup := resp.inGroup, word := resp.word } : PermGroupMembershipResult)))

-- ============================================================================
-- Backend Registration
-- ============================================================================

initialize do
  let stateRef ← IO.mkRef (none : Option OscarSessionState)
  CAS.registerCASBackend {
    name := `Oscar
    priority := 1500  -- between M2 (1000) and SymPy (2000)
    cmd := "julia"
    args := #["./oscar/macaulean_oscar.jl"]
    requestTimeout := 120000  -- Oscar/Julia startup is slow
    supports := fun type =>
      type == .string "reduction_problem" ||
      type == .string "factorization_problem" ||
      type == .string "groebner_basis_problem" ||
      type == .string "radical_membership_problem" ||
      type == .string "poly_factorization_problem" ||
      type == .string "perm_group_membership_problem"
    handleRequest := fun streams request => do
      let state ← match ← stateRef.get with
        | some s => pure s
        | none =>
            let s ← OscarSessionState.new
            stateRef.set (some s)
            pure s
      match request.type with
      | .string "reduction_problem" => handleOscarReduction streams state request
      | .string "factorization_problem" => handleOscarFactorInt streams state request
      | .string "groebner_basis_problem" => handleOscarGroebner streams state request
      | .string "radical_membership_problem" => handleOscarRadical streams state request
      | .string "poly_factorization_problem" => handleOscarPolyFactor streams state request
      | .string "perm_group_membership_problem" => handleOscarPermGroupMembership streams state request
      | _ => pure (.unsupported s!"Oscar does not support: {toJson request.type}")
  }

end Macaulean
