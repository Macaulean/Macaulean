import Macaulean.Verification.Handles.Intro
import Macaulean.Verification.Targets
import Macaulean.Interpreter.DSL

/-!
# Naming worksheet functions in Lean

Two ways to obtain an `Fn` for a worksheet function:

* **Automatic constants.** After every M2 input that binds a function globally, the
  constant `M2.<name> : Fn` is defined (when `m2.expose` is on). It captures the
  worksheet as it is right after that input. If the name is taken, for instance by
  an earlier definition of the same function, the constant is `M2.<name>_<k>`.
* **Live references.** `m2_fn% name` denotes the function bound to `name` at this
  point of the worksheet. It reuses an existing constant for the same function and
  worksheet state, and otherwise defines `M2.<name>_<k>`.

Worksheet states are reflected once per M2 input, as private constants, so that
handles taken between the same two inputs share their state.
-/
register_option m2.expose : Bool := {
  defValue := true
  descr := "Define a Lean constant `M2.<name> : Macaulean.M2.Fn` for every M2 function definition." }

namespace Macaulean.M2.Handles
open Lean Elab Command Term Meta

structure Snapshot where
  key : Nat
  const : Name
  state : Runtime.State

structure Handle where
  const : Name
  key : Nat
  value : Value
  m2name : String

structure Registry where
  snapshots : Array Snapshot := #[]
  handles : Array Handle := #[]
  deriving Inhabited

initialize registryExt : EnvExtension Registry ← registerEnvExtension (pure {})

def getRegistry : CoreM Registry := return registryExt.getState (← getEnv)

def Registry.snapshot? (r : Registry) (const : Name) : Option Snapshot :=
  r.snapshots.find? (·.const == const)

/-- The worksheet state after the most recent input, reflected once. -/
def ensureSnapshot (session : Session) : CoreM Snapshot := do
  let key := session.nextInput
  if let some snap := (← getRegistry).snapshots.find? (·.key == key) then return snap
  let env ← getEnv
  let name := mkPrivateName env (`Macaulean.M2.Handles.worksheet ++ Name.mkSimple s!"state{key}")
  let state : Runtime.State := ⟨session.env, session.heap⟩
  addDecl (.defnDecl {
    name, levelParams := [], type := mkConst ``Runtime.State,
    value := Verification.Targets.stateExpr state, hints := .regular 0, safety := .safe })
  let snap : Snapshot := ⟨key, name, state⟩
  modifyEnv fun env => registryExt.modifyState env fun r => { r with snapshots := r.snapshots.push snap }
  return snap

private def freshName (m2name : String) (key : Nat) : CoreM Name := do
  let env ← getEnv
  let plain := Name.mkStr `M2 m2name
  if !env.contains plain then return plain
  let mut i := 0
  repeat
    let candidate := Name.mkStr `M2 (if i == 0 then s!"{m2name}_{key}" else s!"{m2name}_{key}_{i}")
    if !env.contains candidate then return candidate
    i := i + 1
  return plain

/-- The handle for `m2name` in the current worksheet state, defined if necessary. -/
def ensureHandle (m2name : String) (session : Session) : CoreM Handle := do
  let some value := session.lookup m2name
    | throwError "`{m2name}` is not bound in the M2 worksheet"
  unless Runtime.callable value do
    throwError "`{m2name}` is bound to {value.className}, not to a function"
  let key := session.nextInput
  if let some h := (← getRegistry).handles.find? (fun h => h.key == key && h.value == value) then
    return h
  let snap ← ensureSnapshot session
  let name ← freshName m2name key
  addDecl (.defnDecl {
    name, levelParams := [], type := mkConst ``Fn,
    value := mkApp2 (mkConst ``Fn.mk) (mkConst snap.const) (valueExpr value),
    hints := .regular 0, safety := .safe })
  let h : Handle := ⟨name, key, value, m2name⟩
  modifyEnv fun env => registryExt.modifyState env fun r => { r with handles := r.handles.push h }
  return h

/-- Global names a compiled body reads. -/
partial def globalsRead : Lexical.Code → List String
  | .read (.global x) => [x]
  | .unop _ a | .returnTerm a | .set _ a | .setMany _ a | .polyRing a _ => globalsRead a
  | .binop _ a b | .logic _ a b | .seq a b | .apply a b | .ifThen a b => globalsRead a ++ globalsRead b
  | .ifElse c a b | .indexAssign c a b => globalsRead c ++ globalsRead a ++ globalsRead b
  | .listLit cs | .sequence cs => cs.flatMap globalsRead
  | .lambda _ _ body => globalsRead body
  | _ => []

/-- Define `M2.<name>` for every function bound globally by the last input. -/
def exposeHook (before after : Session) : CommandElabM Unit := do
  unless m2.expose.get (← getOptions) do return
  let fresh := after.env.take (after.env.length - before.env.length)
  let mut seen : List String := []
  for (name, value) in fresh do
    if seen.contains name then continue
    seen := name :: seen
    let .closure id := value | continue
    try
      let h ← liftCoreM <| ensureHandle name after
      if h.const != Name.mkStr `M2 name then
        logInfo m!"the Lean constant for this definition of `{name}` is `{h.const}`"
      if let some (.closure _ _ body _) := after.heap.functions[id]? then
        let missing := (globalsRead body).eraseDups.filter (after.env.lookup · |>.isNone)
        unless missing.isEmpty do
          logInfo m!"`{h.const}` captures the worksheet before {missing} is defined; \
            after defining it, use `m2_fn% {name}`"
    catch e => logWarning m!"could not expose `{name}` to Lean: {e.toMessageData}"

initialize DSL.registerInputHook exposeHook

/-- `m2_fn% name`: the worksheet function `name` at this point of the worksheet. -/
syntax (name := m2fnTerm) "m2_fn% " ident : term

@[term_elab m2fnTerm]
def elabM2Fn : TermElab := fun stx _ => do
  let name := stx[1].getId.toString
  let session := DSL.sessionExt.getState (← getEnv)
  let h ← ensureHandle name session
  return mkConst h.const

end Macaulean.M2.Handles
