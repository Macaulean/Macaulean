import Macaulean.Interpreter.RuntimeExpr
import Macaulean.Interpreter.Session

/-!
# Persistent Lean definitions for M2 worksheets

Each export is a closed snapshot, not a reference into the elaborator's mutable
session. Original names never change meaning; later versions live under `.v2`,
`.v3`, etc. Calls return the resulting state, so returned closures and effects
remain meaningful. Exporting does not execute a function or assert its contract.
-/
namespace Macaulean.M2.DefinitionExposure
open Lean Elab Command Meta

/-- Execute an exported function in its captured worksheet state. -/
def run (fn : Value) (state : Runtime.State) (fuel : Nat) (arg : Value) :
    Except Error (Value × Runtime.State) :=
  Runtime.finish (Runtime.call fuel fn arg state)

structure Entry where
  binding : String
  root : Name
  latest : Name
  revision : Nat
  deriving Inhabited

initialize exportsExt : EnvExtension (List Entry) ← registerEnvExtension (pure [])
initialize snapshotExt : EnvExtension Nat ← registerEnvExtension (pure 0)
initialize literalsExt : EnvExtension (ExprMap Name) ← registerEnvExtension (pure {})

/-- Most recent export in this worksheet; declarations themselves survive imports. -/
def latest (binding : String) : CommandElabM (Option Name) := do
  return ((exportsExt.getState (← getEnv)).find? (·.binding == binding)).map (·.latest)

private def visible (s : Session) : List (String × Value) :=
  let names := (s.scope.names.map Prod.fst ++ s.env.map Prod.fst).eraseDups
  names.filterMap fun name => (fun value => (name,value)) <$> s.lookup name

mutual
/-- Handles anywhere inside a collection need a refreshed state snapshot. -/
private def usesState : Value → Bool
  | .closure _ | .symbol .. => true
  | .list xs | .sequence xs => anyState xs
  | .algebra (.library _) | .algebra (.builtin _) => true
  | _ => false
private def anyState : List Value → Bool
  | [] => false
  | x :: xs => usesState x || anyState xs
end

private def defineRaw (name : Name) (value : Expr) (doc : String) : CommandElabM Unit :=
  liftTermElabM do
    if (← getEnv).contains name then
      throwError "M2 generated declaration already exists: {name}"
    let type ← inferType value
    addAndCompile (.defnDecl {
      name, levelParams := [], type, value, hints := .regular 0, safety := .safe }) (logCompileErrors := false)
    addDocStringCore name doc
    addDeclarationRangesFromSyntax name (← getRef)

/-- Bound constructor-list depth in generated declarations. Large heaps must not
require users to raise Lean's compiler recursion limit. Every auxiliary is a
transparent, kernel-checked definition; no serialization oracle is involved. -/
private def intern (owner : Name) (value : Expr) (serial : Nat) :
    CommandElabM (Expr × Nat) := do
  if let some name := (literalsExt.getState (← getEnv))[value]? then
    return (mkConst name,serial)
  let name := owner ++ Name.mkSimple s!"_part{serial}"
  defineRaw name value "Shared closed literal in an M2 snapshot."
  modifyEnv fun env => literalsExt.setState env ((literalsExt.getState env).insert value name)
  return (mkConst name,serial + 1)

private partial def shareLists (owner : Name) (e : Expr) (serial : Nat) :
    CommandElabM (Expr × Nat) := do
  if let some name := (literalsExt.getState (← getEnv))[e]? then
    return (mkConst name,serial)
  if e.isAppOfArity ``List.cons 3 && !e.hasLooseBVars then
    let elementType := e.getAppArgs[0]!
    let cons := e.getAppFn
    let mut items : Array Expr := #[]
    let mut tail := e
    while tail.isAppOfArity ``List.cons 3 do
      let args := tail.getAppArgs
      items := items.push args[1]!
      tail := args[2]!
    let (sharedTail,serial) ← shareLists owner tail serial
    let nil := mkApp (mkConst ``List.nil cons.constLevels!) elementType
    let mut serial := serial
    let mut chunks : Array Expr := #[]
    let mut chunk : Array Expr := #[]
    for item in items do
      let (item,next) ← shareLists owner item serial
      serial := next
      chunk := chunk.push item
      if chunk.size == 32 then
        let value := chunk.foldr (fun item rest => mkApp3 cons elementType item rest) nil
        let (value,next) ← intern owner value serial
        serial := next
        chunks := chunks.push value
        chunk := #[]
    let mut result := chunk.foldr (fun item rest => mkApp3 cons elementType item rest) sharedTail
    let levels := cons.constLevels!
    for part in chunks.reverse do
      result := mkApp3 (mkConst ``List.append levels) elementType part result
    return (result,serial)
  else
    match e with
    | .app f a =>
      let (f,serial) ← shareLists owner f serial
      let (a,serial) ← shareLists owner a serial
      let result := mkApp f a
      -- Closure records and algebra objects recur across many cells and revisions.
      let head := e.getAppFn.constName?
      if head.any (fun n => n.getPrefix == ``Runtime.Function || n.getPrefix == ``Polynomials.Object) &&
          !e.hasLooseBVars then
        let (value,serial) ← intern owner result serial
        modifyEnv fun env => literalsExt.setState env ((literalsExt.getState env).insert e value.constName!)
        return (value,serial)
      return (result,serial)
    | _ => return (e,serial)

private def define (name : Name) (value : Expr) (doc : String) : CommandElabM Unit := do
  let (shared,_) ← shareLists name value 0
  defineRaw name shared doc
  unless (literalsExt.getState (← getEnv)).contains value do
    modifyEnv fun env => literalsExt.setState env ((literalsExt.getState env).insert value name)

private def equation (name target : Name) (rhs : Expr) : CommandElabM Unit :=
  liftTermElabM do
    let value ← mkEqRefl rhs
    let type ← mkEq (mkConst target) rhs
    addDecl (.thmDecl { name, levelParams := [], type, value })
    addDeclarationRangesFromSyntax name (← getRef)
    addDocStringCore name "Definitional equation for this M2 export; not a mathematical correctness contract."

/-- Use native Lean data where no runtime dispatch is needed. -/
private def native (v : Value) : CommandElabM Expr := do
  match v with
  | .zz n => return toExpr n
  | .qq q => return algebraRatExpr q
  | .bool b => return toExpr b
  | .list xs | .sequence xs => return toExpr xs
  | .algebra (.ring r) => return algebraRingExpr r
  | .algebra (.poly r raw) =>
    let p ← match Polynomials.decode r.names.length raw with
      | .ok p => pure p
      | .error e => throwError "cannot expose polynomial: {e}"
    letI : ToExpr Rat := ⟨algebraRatExpr, mkConst ``Rat⟩
    return toExpr p
  | _ => return valueExpr v

/-- Encode the native export back into the exact runtime value. -/
private def encoded (v : Value) (name : Name) : Expr :=
  let x := mkConst name
  match v with
  | .zz _ => mkApp (mkConst ``Value.zz) x
  | .qq _ => mkApp (mkConst ``Value.qq) x
  | .bool _ => mkApp (mkConst ``Value.bool) x
  | .list _ => mkApp (mkConst ``Value.list) x
  | .sequence _ => mkApp (mkConst ``Value.sequence) x
  | .algebra (.ring _) => mkApp (mkConst ``Value.algebra) (mkApp (mkConst ``Polynomials.Object.ring) x)
  | .algebra (.poly r _) =>
    mkApp (mkConst ``Value.algebra) <| mkApp2 (mkConst ``Polynomials.Object.poly)
      (algebraRingExpr r) (mkApp2 (mkConst ``Polynomials.encode) (toExpr r.names.length) x)
  | _ => x

/-- Publish after a successful input, using its result rather than running it again.
State-dependent exports are refreshed conservatively on any runtime state change,
including writes to captured cells that leave the closure handle unchanged. -/
def record (term : Term) (before after : Session) : CommandElabM Unit := do
  let mut entries := exportsExt.getState (← getEnv)
  let state : Runtime.State := ⟨after.env, after.heap⟩
  let stateValue := RuntimeExpr.stateExpr state
  let changedState := RuntimeExpr.stateExpr ⟨before.env,before.heap⟩ != stateValue
  let selected := (visible after).filter fun (name,value) =>
    before.lookup name != some value ||
      (changedState && usesState value && entries.any (·.binding == name))
  if selected.isEmpty then return
  let moduleName := (← getEnv).mainModule
  let ns ← getCurrNamespace
  let scope := if ns.isAnonymous then moduleName else ns
  let serial := snapshotExt.getState (← getEnv) + 1
  let snapshot := moduleName ++ `M2Snapshots ++ Name.mkSimple s!"s{serial}"
  define snapshot stateValue "Runtime state after this successful M2 input."
  let (code,_,_) := Lexical.prepare term before.scope
  for (binding,value) in selected do
    let prior := entries.find? (·.binding == binding)
    let root := prior.map (·.root) |>.getD (scope ++ `M2Generated ++ Name.mkSimple binding)
    let revision := (prior.map (·.revision)).getD 0 + 1
    let name := if revision == 1 then root else root ++ Name.mkSimple s!"v{revision}"
    define (name ++ `value) (valueExpr value) "Exact M2 runtime value; handles are relative to this export's state."
    define (name ++ `state) (mkConst snapshot) "Captured runtime state for this revision."
    let body := match value with
      | .closure id => match after.heap.functions[id]? with
        | some (.closure params slots body _) => Lexical.Code.lambda params slots body
        | _ => code
      | .algebra (.library lib) => (Library.lookup lib).getD code
      | _ => code
    define (name ++ `code) (toExpr body) "Lowered M2 code: the lambda for closures, or the defining input for other values."
    let rhs ← if Runtime.callable value then
      pure <| mkApp2 (mkConst ``run) (mkConst (name ++ `value)) (mkConst (name ++ `state))
      else native value
    define name rhs s!"M2 binding {binding}, revision {revision}. Immutable snapshot; inspect .value, .state, .code, and .definition."
    equation (name ++ `definition) name rhs
    unless Runtime.callable value do
      equation (name ++ `value_eq) (name ++ `value) (encoded value name)
    entries := { binding,root,latest := name,revision } :: entries.filter (·.binding != binding)
  modifyEnv fun env => snapshotExt.setState (exportsExt.setState env entries) serial

syntax (name := definitionCommand) "#m2_definition " str : command

@[command_elab definitionCommand]
def elabDefinition : CommandElab := fun stx => do
  let binding := (⟨stx[1]⟩ : TSyntax `str).getString
  let some name ← latest binding | throwErrorAt stx "no Lean definition exported for M2 binding {binding}"
  logInfoAt stx m!"{MessageData.ofConstName name}\nInspect with #print {name}, #print {name}.code, or #print {name}.definition"

end Macaulean.M2.DefinitionExposure
