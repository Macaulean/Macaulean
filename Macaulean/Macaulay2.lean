import Lean.Data.JsonRpc
import Lean.Data.Json
--We aren't technically using LSP
--but I'm using the LSP base protocol to
--send the messages
import Lean.Data.Lsp.Communication
import MRDI.Basic
import MRDI.Poly

--TODO: consider framing this as a monad instead
structure Macaulay2 where
  requestStream : IO.FS.Stream
  responseStream : IO.FS.Stream
  nextRequestId : IO.Ref Nat

structure SosSummand where
  weight : Nat
  poly : MRDI.PolynomialData
  deriving Repr, Lean.ToJson, Lean.FromJson

structure SosCertificate where
  ok : Bool
  status : String
  scale : Nat
  summands : Array SosSummand
  deriving Repr, Lean.ToJson, Lean.FromJson

structure SosCertificateRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  deriving Repr, Lean.ToJson, Lean.FromJson

def startM2Server : IO (IO.Process.Child {stdin := .null, stdout := .piped, stderr := .inherit} × Macaulay2) :=
  do let (m2stdin,m2Process) <-
      IO.Process.spawn {cmd := "M2"
                       , args := #["--script", "./macaulean.m2"]
                       , cwd := .some "./m2/"
                       , env := .empty
                       , inheritEnv := true
                       , setsid := false
                       , stdin := .piped
                       , stdout := .piped} >>=
      IO.Process.Child.takeStdin
     let m2stdinStream :=
        IO.FS.Stream.ofHandle m2stdin
     let m2stdoutStream :=
        IO.FS.Stream.ofHandle m2Process.stdout
     (m2Process,.) <$> .mk m2stdinStream m2stdoutStream <$> IO.mkRef 1

initialize macaulay2ServerRef : IO.Ref (Option Macaulay2)
  ← IO.mkRef .none

def globalM2Server : IO Macaulay2 :=
  do match (← macaulay2ServerRef.get) with
    | .some m2server => pure m2server
    | .none => do let (_,server) <- startM2Server
                  let server' <- macaulay2ServerRef.modifyGet (fun
                    | .none => (server, .some server)
                    | .some otherServer => (otherServer, .some otherServer))
                  pure server'

def Macaulay2.sendRequest [Lean.ToJson a] [Lean.FromJson b] (m2 : Macaulay2) (requestName : String) (requestBody : a) : IO b := do
  let reqId ←
    Lean.JsonRpc.RequestID.num <$> m2.nextRequestId.modifyGet (fun x => (x,x+1))
  m2.requestStream.writeLspRequest
    { id := reqId
      method := requestName
      param :=  requestBody }
  let response <- m2.responseStream.readLspResponseAs reqId (α := b)
  pure response.result

def Macaulay2.eval (m2 : Macaulay2) (cmd : String) : IO String :=
  m2.sendRequest "testMethod" [cmd]

def Macaulay2.factorNat (m2 : Macaulay2) (x : Nat) : IO (List (Nat × Nat)) := do
  let response : List (List Nat) ← m2.sendRequest "factorInt" [x]
  pure ((fun p =>
    match p with
      | [a,b] => (a,b)
      | _ => ⟨1,1⟩) <$> response)

def Macaulay2.quotientRemainderMrdi (m2 : Macaulay2) (poly ideal : Mrdi) : IO (Mrdi × Mrdi) := do
  let response : Array Mrdi ← m2.sendRequest "quotientRemainder" #[poly, ideal]
  let some q := response[0]?
    | throw <| IO.userError "Macaulay2 quotientRemainder returned no quotient"
  let some r := response[1]?
    | throw <| IO.userError "Macaulay2 quotientRemainder returned no remainder"
  pure (q, r)

structure QuotientRemainderPolyRequest where
  numVars : Nat
  polyData : MRDI.PolynomialData
  idealData : Array MRDI.PolynomialData
  deriving Repr, Lean.ToJson, Lean.FromJson

structure QuotientRemainderPolyResponse where
  ok : Bool
  status : String
  quotients : Array MRDI.PolynomialData
  remainder : MRDI.PolynomialData
  deriving Repr, Lean.ToJson, Lean.FromJson

def Macaulay2.quotientRemainderPolyData (m2 : Macaulay2) (numVars : Nat)
    (polyData : MRDI.PolynomialData) (idealData : Array MRDI.PolynomialData) :
    IO QuotientRemainderPolyResponse := do
  let req : QuotientRemainderPolyRequest := {
    numVars := numVars
    polyData := polyData
    idealData := idealData
  }
  m2.sendRequest "quotientRemainderPolyData" req

def Macaulay2.sosCertificateData (m2 : Macaulay2) (numVars : Nat)
    (polyData : MRDI.PolynomialData) : IO SosCertificate := do
  let req : SosCertificateRequest := {
    numVars := numVars
    polyData := polyData
  }
  m2.sendRequest "sosCertificate" req
