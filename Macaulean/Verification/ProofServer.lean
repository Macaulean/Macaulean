import Macaulean.Verification.ProofCore

/-! Read-only export for explicitly launched proof workers. Source intent must
already be approved; this RPC never approves a contract or starts a process. -/
namespace Macaulean.M2.Verification.ProofServer
open Lean Lean.Server Lean.Server.RequestM
structure Query where
  position : Lsp.Position
  version : Nat
  binding : String
  schema : String
  deriving FromJson, ToJson
@[server_rpc_method]
def getJob (query : Query) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  if doc.meta.version != query.version then
    throwThe RequestError ⟨.invalidParams,"stale proof job request: document version changed"⟩
  let some kind := Contracts.Kind.parse query.schema
    | throwThe RequestError ⟨.invalidParams,"unknown contract schema"⟩
  let pos := doc.meta.text.lspPosToUtf8Pos query.position
  withWaitFindSnap doc
    (notFoundX := throwThe RequestError ⟨.invalidParams,"no elaboration snapshot"⟩)
    (fun snapshot => snapshot.endPos >= pos)
    (fun snapshot => do
      let index := Index.indexExt.getState snapshot.env
      let some entry := index.find query.binding
        | throwThe RequestError ⟨.invalidParams,"unknown proof binding"⟩
      let some proposal := index.ledger.find entry.id kind
        | throwThe RequestError ⟨.invalidParams,"no contract proposed"⟩
      let job ← match ProofCore.jobAt snapshot.env query.binding kind proposal.digest with
        | .ok job => pure job
        | .error error => throwThe RequestError ⟨.invalidParams,error⟩
      pure <| Json.mkObj [("uri",toJson doc.meta.uri),("documentVersion",toJson doc.meta.version),
        ("position",toJson query.position),("job",ProofCore.jobJson job)])
end Macaulean.M2.Verification.ProofServer
