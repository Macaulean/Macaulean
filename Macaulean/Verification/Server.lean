import Macaulean.Verification.Panel

/-!
# Versioned read-only access for editor and future agent clients

A client supplies the document version it inspected. Mismatched versions are
rejected before reading the semantic index. Responses identify the immutable
snapshot and must be discarded by a client that has since observed another edit.
There is deliberately no approval or proof-acceptance RPC.
-/
namespace Macaulean.M2.Verification.Server
open Lean Lean.Server Lean.Server.RequestM

structure Query where
  position : Lsp.Position
  version : Nat
  deriving FromJson, ToJson

@[server_rpc_method]
def getSnapshot (query : Query) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  if doc.meta.version != query.version then
    throwThe RequestError ⟨.invalidParams,"stale M2 snapshot request: document version changed"⟩
  let pos := doc.meta.text.lspPosToUtf8Pos query.position
  withWaitFindSnap doc
    (notFoundX := throwThe RequestError ⟨.invalidParams,"no M2 elaboration snapshot at this position"⟩)
    (fun snapshot => snapshot.endPos >= pos)
    (fun snapshot => pure (Json.mkObj [
      ("schema",Json.str "macaulean.semantic-snapshot.v1"),
      ("uri",toJson doc.meta.uri), ("documentVersion",toJson doc.meta.version),
      ("position",toJson query.position), ("snapshotEndByte",toJson snapshot.endPos.byteIdx),
      ("index",Panel.inventory snapshot.env)]))

end Macaulean.M2.Verification.Server
