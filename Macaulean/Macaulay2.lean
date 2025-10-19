import Lean.Data.JsonRpc
import Lean.Data.Json
--We aren't technically using LSP
--but I'm using the LSP base protocol to
--send the messages
import Lean.Data.Lsp.Communication

--TODO: consider framing this as a monad instead
structure Macaulay2 where
  requestStream : IO.FS.Stream
  responseStream : IO.FS.Stream
  nextRequestId : IO.Ref Nat

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

abbrev Poly := List (Int × Nat)
def Macaulay2.factorUnivariatePoly (m2 : Macaulay2) (p : Poly) : IO (List (Poly × Nat)) := do
  let response : List (Poly × Nat) ← m2.sendRequest "factorUnivariatePoly" [p]
  return response
