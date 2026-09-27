import Macaulean.Verification.Intent
import Macaulean.Interpreter.Session

/-!
# File-local M2 semantic index

The index follows Lean's immutable command environments. Binding IDs are qualified
by the Lean module; generations distinguish rebinding within a worksheet. Source
ranges do not participate in semantic keys. A failed M2 input cannot create a new
binding because only the committed before/after sessions are compared.
-/
namespace Macaulean.M2.Verification.Index
open Lean Elab Command

structure SourceNode where
  path : List Nat
  kind : String
  startByte : Nat
  stopByte : Nat
  deriving Repr, Inhabited, ToJson, FromJson

/-- Paths index original syntax children, not guessed program counters. -/
def sourceNodes (fuel : Nat) (stx : Syntax) (path : List Nat := []) : List SourceNode :=
  match fuel with
  | 0 => []
  | fuel+1 =>
    let here := match stx.getPos?,stx.getTailPos? with
      | some a,some b => [⟨path,stx.getKind.toString,a.byteIdx,b.byteIdx⟩]
      | _,_ => []
    here ++ (stx.getArgs.toList.zip (List.range stx.getArgs.size)).flatMap
      (fun (child,i) => sourceNodes fuel child (path ++ [i]))

structure Entry where
  id : String
  name : String
  generation : Nat
  sourceFile : String
  declarationKey : String
  nodes : List SourceNode
  deriving Inhabited

structure State where
  entries : List Entry := []
  ledger : Intent.Ledger := {}
  deriving Inhabited

initialize indexExt : EnvExtension State ← registerEnvExtension (pure {})

def get : CommandElabM State := return indexExt.getState (← getEnv)
def put (s : State) : CommandElabM Unit := modifyEnv fun env => indexExt.setState env s

def State.find (s : State) (name : String) : Option Entry :=
  s.entries.find? (fun entry => entry.name == name)

def visible (s : Session) : List (String × Value) :=
  let names := (s.scope.names.map Prod.fst ++ s.env.map Prod.fst).eraseDups
  names.filterMap fun name => (fun value => (name,value)) <$> s.lookup name

/-- The command's resolved representation is recorded, but execution is not run a
second time. Heap mutations in existing closures are detected by revision queries. -/
def record (stx : Syntax) (term : Term) (before after : Session) : CommandElabM (List Entry) := do
  let mut index ← get
  let env ← getEnv
  let file ← getFileName
  let (code,_,_) := Lexical.prepare term before.scope
  let declarationKey := Snapshot.exprKey (LibraryCompiler.codeExpr code)
  let nodes := sourceNodes 4096 stx
  let mut changed : List Entry := []
  for (name,value) in visible after do
    unless before.lookup name == some value do
      let generation := ((index.find name).map (·.generation)).getD 0 + 1
      let entry : Entry := {
        id := Snapshot.bindingId env.mainModule name, name, generation,
        sourceFile := file, declarationKey, nodes }
      index := { index with entries := entry :: index.entries.filter (fun e => e.name != name) }
      changed := changed ++ [entry]
  put index
  return changed

/-- Library functions can be inspected before a user binding is created. They are
explicitly labelled as library entries: no fake source coordinates are invented. -/
def ensure (name : String) (session : Session) : CommandElabM Entry := do
  let mut index ← get
  if let some entry := index.find name then return entry
  let some value := session.lookup name | throwError "unknown M2 binding {name}"
  unless Runtime.callable value do throwError "{name} is not callable"
  let origin := match value with
    | .algebra (.library _) => "Macaulean/Interpreter/Buchberger.m2"
    | _ => "<runtime binding>"
  let entry : Entry := {
    id := Snapshot.bindingId (← getEnv).mainModule name, name, generation := 0,
    sourceFile := origin, declarationKey := Snapshot.exprKey (Macaulean.M2.valueExpr value), nodes := [] }
  index := { index with entries := entry::index.entries }
  put index
  return entry

def currentPayload (entry : Entry) (kind : Contracts.Kind) (session : Session)
    (theory : Snapshot.Theory) : Except String String := do
  let some value := session.lookup entry.name | .error "binding is no longer visible"
  unless Runtime.callable value do .error "binding is no longer callable"
  let semantic ← Snapshot.approvalPayload theory entry.id kind value ⟨session.env,session.heap⟩
  return Fingerprint.frame [semantic,entry.declarationKey,toString entry.generation]

def viewLabels (v : Value) : List String :=
  match v with
  | .algebra (.poly r _) =>
    if (Views.readPolynomial r v).isOk then
      ["Checked ring-indexed polynomial view", "Coefficientwise interpretation; not a proof of an algorithm"]
    else ["Polynomial view unavailable: malformed dimension"]
  | .algebra (.row r ps) =>
    if (Views.readRow r ps.length v).isOk then ["Checked dimension-indexed coefficient/generator row"]
    else ["Row view unavailable: malformed dimensions"]
  | .closure _ | .algebra (.library _) | .algebra (.builtin _) =>
    ["Lexical computation; no pure-function view is assumed"]
  | _ => ["No polynomial or coefficient-row view for this value"]

end Macaulean.M2.Verification.Index
