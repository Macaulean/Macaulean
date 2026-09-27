import Macaulean.Verification.Contracts
import Macaulean.Verification.Fingerprint
import Macaulean.Interpreter.Check
import Macaulean.Interpreter.LibraryCompiler

/-!
# Semantic snapshots, not source-text guesses

Keys retain constructor structure, resolved code, reachable global bindings,
captured cells, library bodies and ring identities. Comments and source offsets
are deliberately absent. Theory fingerprints traverse actual declaration bodies,
including the formal contract. Missing dependencies or exhausted budgets fail
closed. Session-relative handles are deliberately not portable.
-/
namespace Macaulean.M2.Verification.Snapshot
open Lean Fingerprint Lexical

def nameKey : Name → String
  | .anonymous => frame ["name"]
  | .str p s => frame ["str",nameKey p,s]
  | .num p n => frame ["num",nameKey p,toString n]

def levelKey : Level → String
  | .zero => "zero"
  | .succ u => frame ["succ",levelKey u]
  | .max u v => frame ["max",levelKey u,levelKey v]
  | .imax u v => frame ["imax",levelKey u,levelKey v]
  | .param n => frame ["param",nameKey n]
  | .mvar n => frame ["mvar",nameKey n.name]

def binderKey : BinderInfo → String
  | .default => "default" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"

def exprKey : Expr → String
  | .bvar i => frame ["bvar",toString i]
  | .fvar i => frame ["fvar",nameKey i.name]
  | .mvar i => frame ["mvar",nameKey i.name]
  | .sort u => frame ["sort",levelKey u]
  | .const n us => frame ["const",nameKey n,frame (us.map levelKey)]
  | .app f a => frame ["app",exprKey f,exprKey a]
  | .lam _ t b bi => frame ["lam",binderKey bi,exprKey t,exprKey b]
  | .forallE _ t b bi => frame ["forall",binderKey bi,exprKey t,exprKey b]
  | .letE _ t v b nondep => frame ["let",toString nondep,exprKey t,exprKey v,exprKey b]
  | .lit (.natVal n) => frame ["nat",toString n]
  | .lit (.strVal s) => frame ["string",s]
  | .mdata _ e => exprKey e
  | .proj n i e => frame ["proj",nameKey n,toString i,exprKey e]

def exprNames : Expr → List Name
  | .const n _ => [n]
  | .app f a => exprNames f ++ exprNames a
  | .lam _ t b _ | .forallE _ t b _ => exprNames t ++ exprNames b
  | .letE _ t v b _ => exprNames t ++ exprNames v ++ exprNames b
  | .mdata _ e => exprNames e
  | .proj n _ e => n :: exprNames e
  | _ => []

def declarationExtra (c : ConstantInfo) : List String × List Name :=
  match c with
  | .axiomInfo _ => (["axiom"],[])
  | .defnInfo _ => (["definition",toString c.isPartial],c.all)
  | .thmInfo _ => (["theorem"],c.all)
  | .opaqueInfo _ => (["opaque"],c.all)
  | .quotInfo v => (["quotient",match v.kind with
      | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"],[])
  | .inductInfo v => (["inductive",toString v.numParams,toString v.numIndices,
      frame (v.ctors.map nameKey)],v.all ++ v.ctors)
  | .ctorInfo v => (["constructor",nameKey v.induct,toString v.cidx,
      toString v.numParams,toString v.numFields],[v.induct])
  | .recInfo v =>
    (["recursor",toString v.numParams,toString v.numIndices,toString v.numMotives,
      toString v.numMinors,frame (v.rules.map fun rule =>
        frame [nameKey rule.ctor,toString rule.nfields,exprKey rule.rhs])],
      v.rules.flatMap fun rule => rule.ctor :: exprNames rule.rhs)

structure Theory where
  payload : String
  digest : String
  declarations : List String
  axioms : List String
  deriving Inhabited

private def theoryWalk : Nat → Environment → List Name → List Name → List String → List String →
    Except String (List Name × List String × List String)
  | 0, _, _, _, _, _ => .error "semantic dependency traversal exhausted"
  | _+1, _, [], seen, entries, axioms => .ok (seen,entries,axioms)
  | fuel+1, env, n::todo, seen, entries, axioms => do
    if n ∈ seen then theoryWalk fuel env todo seen entries axioms
    else
      let some c := env.find? n | .error s!"missing semantic declaration {n}"
      let (extra,more) := declarationExtra c
      let value := c.value? true
      let key := frame ([nameKey n,frame (c.levelParams.map nameKey),exprKey c.type,
        toString c.isUnsafe,match value with | none => "no-value" | some e => frame ["value",exprKey e]] ++ extra)
      let refs := exprNames c.type ++ (value.map exprNames).getD [] ++ more
      theoryWalk fuel env (refs ++ todo) (n::seen) (key::entries)
        (if c.isAxiom then n.toString::axioms else axioms)

/-- Exact declaration payload is retained; digest is the portable attestation key. -/
def sealTheory (env : Environment) (roots : List Name) (fuel : Nat := 500000) : Except String Theory := do
  let (seen,entries,axioms) ← theoryWalk fuel env roots [] [] []
  let payload := frame ["lean-declarations-v1",Lean.versionString,frame entries]
  return ⟨payload,sha256 payload,seen.map Name.toString,axioms⟩

def roots : List Name := [
  ``Runtime.evaluate, ``Runtime.call, ``Lexical.prepare, ``Library.definitions,
  ``LibraryCompiler.compile, ``Contracts.Statement, ``Contracts.render,
  ``Views.readPolynomial, ``Views.readRow, ``Fingerprint.sha256]

/-- Lean declarations are immutable within an environment. This cache is local to
the current elaboration environment and does not survive importing a worksheet. -/
initialize theoryExt : EnvExtension (Option Theory) ← registerEnvExtension (pure none)

def theory : Lean.Elab.Command.CommandElabM Theory := do
  if let some result := theoryExt.getState (← getEnv) then return result
  let result ← match sealTheory (← getEnv) roots with
    | .ok result => pure result | .error e => throwError e
  modifyEnv fun env => theoryExt.setState env (some result)
  return result

mutual
/-- Globals read or written by a body, including code inside nested lambdas.
Captured lexical frames are handled separately; closures are not assumed pure. -/
def references : Code → List Ref
  | .int _ | .empty => []
  | .read r => [r]
  | .unop _ a | .returnTerm a => references a
  | .binop _ a b | .logic _ a b | .ifThen a b | .seq a b | .apply a b => references a ++ references b
  | .ifElse a b c | .indexAssign a b c => references a ++ references b ++ references c
  | .set r a => r :: references a
  | .setMany rs a => rs ++ references a
  | .listLit xs | .sequence xs => referencesMany xs
  | .lambda _ _ body => references body
  | .symbol _ r => [r]
  | .polyRing a names => references a ++ names.map Prod.snd
def referencesMany : List Code → List Ref
  | [] => [] | a::as => references a ++ referencesMany as
end

inductive Work where
  | value (v : Value)
  | global (name : String)
  | cell (id : Nat)
  | function (id : Nat)
  | library (name : String)
  deriving Inhabited

def globals (body : Code) : List Work := (references body).filterMap fun
  | .global name => some (.global name) | _ => none

def functionData (f : Runtime.Function) : String × List Work :=
  match f with
  | .closure params slots body captured =>
    (frame ["closure",exprKey (toExpr params),toString slots,
      exprKey (LibraryCompiler.codeExpr body),exprKey (toExpr captured)],
      (captured.flatten.map Work.cell) ++ globals body)
  | .composition a b => ("composition",[.value a,.value b])
  | .predicate op a b => (frame ["predicate",exprKey (toExpr op)],[.value a,.value b])
  | .negated f => ("negated",[.value f])

private def walk : Nat → Runtime.State → List Work → List String → List String →
    Except String (List String)
  | 0, _, _, _, _ => .error "reachable M2 dependency traversal exhausted"
  | _+1, _, [], _, entries => .ok entries
  | fuel+1, state, item::todo, seen, entries => do
    match item with
    | .value v =>
      let key := frame ["value",exprKey (Macaulean.M2.valueExpr v)]
      let children := match v with
        | .list xs | .sequence xs => xs.map Work.value
        | .closure id => [Work.function id]
        | .symbol _ id => [Work.cell id]
        | .algebra (.library name) => [Work.library name]
        | _ => []
      walk fuel state (children ++ todo) seen (key::entries)
    | .global name =>
      let key := frame ["global",name]
      if key ∈ seen then walk fuel state todo seen entries
      else
        match state.env.lookup name with
        | none => walk fuel state todo (key::seen) (frame [key,"unbound"]::entries)
        | some v => walk fuel state (.value v::todo) (key::seen) (key::entries)
    | .cell id =>
      let key := frame ["cell",toString id]
      if key ∈ seen then walk fuel state todo seen entries
      else
        let some v := state.heap.cells[id]? | .error "invalid captured cell in semantic snapshot"
        walk fuel state (.value v::todo) (key::seen) (key::entries)
    | .function id =>
      let key := frame ["function",toString id]
      if key ∈ seen then walk fuel state todo seen entries
      else
        let some f := state.heap.functions[id]? | .error "invalid function in semantic snapshot"
        let (data,children) := functionData f
        walk fuel state (children ++ todo) (key::seen) (frame [key,data]::entries)
    | .library name =>
      let key := frame ["library",name]
      if key ∈ seen then walk fuel state todo seen entries
      else
        let some code := Library.lookup name | .error "unknown M2 library dependency"
        walk fuel state (globals code ++ todo) (key::seen)
          (frame [key,exprKey (LibraryCompiler.codeExpr code)]::entries)

def reachable (fn : Value) (state : Runtime.State) : Except String String := do
  let entries ← walk 100000 state [.value fn] [] []
  return frame ["m2-reachable-v1",toString state.heap.nextRing,frame entries]

/-- Display identity is stable under comments/formatting. Rebinding and changing
captured/global dependencies affect the revision, independently of source spans. -/
def bindingId (moduleName : Name) (name : String) : String :=
  sha256 (frame ["m2-binding-v1",nameKey moduleName,name])

def approvalPayload (theory : Theory) (id : String) (kind : Contracts.Kind)
    (fn : Value) (state : Runtime.State) : Except String String := do
  return frame [Contracts.version,id,kind.name,Contracts.render kind,theory.digest,
    ← reachable fn state]

end Macaulean.M2.Verification.Snapshot
