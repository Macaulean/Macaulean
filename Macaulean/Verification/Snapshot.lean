import Macaulean.Verification.Contracts
import Macaulean.Verification.ExpressionGraph
import Macaulean.Interpreter.Check
import Macaulean.Interpreter.LibraryCompiler

/-!
# Semantic snapshots

Declaration types and bodies are encoded as shared constructor graphs before
hashing. The retained manifest contains each declaration's name and SHA-256,
not exponentially expanded copies of every expression tree. Every referenced
declaration is visited, including proof bodies and recursor rules. Hash equality
relies on collision resistance; missing dependencies and exhausted budgets fail
closed. Exact proposed runtime expressions are still checked when installed.
-/
namespace Macaulean.M2.Verification.Snapshot
open Lean Fingerprint Lexical

def nameKey := ExpressionGraph.nameKey
def levelKey := ExpressionGraph.levelKey
def binderKey := ExpressionGraph.binderKey
def exprKey := ExpressionGraph.key
def exprNames (e : Expr) := (ExpressionGraph.encodeMany [e]).constants

/-- Non-expression declaration fields and additional semantic edges. Recursor
rule expressions are encoded together with the type/body below. -/
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
        frame [nameKey rule.ctor,toString rule.nfields])],v.rules.map (·.ctor))

structure Theory where
  /-- Complete, ordered declaration-name/digest manifest. -/
  payload : String
  digest : String
  declarations : List String
  axioms : List String
  deriving Inhabited

private def theoryWalk : Nat → Environment → List Name → NameSet → List Name →
    List String → List String → Except String (List Name × List String × List String)
  | 0, _, _, _, _, _, _ => .error "semantic dependency traversal exhausted"
  | _+1, _, [], _, visited, entries, axioms => .ok (visited,entries,axioms)
  | fuel+1, env, n::todo, scheduled, visited, entries, axioms => do
    let some c := env.find? n | .error s!"missing semantic declaration {n}"
    let (extra,more) := declarationExtra c
    let value := c.value? true
    let ruleExprs := match c with | .recInfo v => v.rules.map (·.rhs) | _ => []
    let expressions := c.type :: (value.toList ++ ruleExprs)
    let graph := ExpressionGraph.encodeMany expressions
    let key := frame ([nameKey n,frame (c.levelParams.map nameKey),
      toString c.isUnsafe,toString value.isSome,graph.payload] ++ extra)
    let refs := (graph.constants ++ more).foldl (fun names ref => names.insert ref) ({} : NameSet)
    let fresh := refs.toArray.toList.filter (fun ref => !scheduled.contains ref)
    let scheduled := fresh.foldl (fun names ref => names.insert ref) scheduled
    let manifestEntry := frame [nameKey n,sha256 key]
    theoryWalk fuel env (fresh ++ todo) scheduled (n::visited) (manifestEntry::entries)
      (if c.isAxiom then n.toString::axioms else axioms)

/-- All edges are scheduled exactly once. The budget counts unique declarations,
not repeated references in generated code. -/
def sealTheory (env : Environment) (roots : List Name) (fuel : Nat := 500000) : Except String Theory := do
  let initial := roots.foldl (fun names n => names.insert n) ({} : NameSet)
  let (seen,entries,axioms) ← theoryWalk fuel env initial.toArray.toList initial [] [] []
  let payload := frame ["lean-declaration-manifest-v2",Lean.versionString,frame entries]
  return ⟨payload,sha256 payload,seen.map Name.toString,axioms⟩

def roots : List Name := [
  ``Runtime.evaluate, ``Runtime.call, ``Lexical.prepare, ``Library.definitions,
  ``LibraryCompiler.compile, ``Contracts.Statement, ``Contracts.render,
  ``Views.readPolynomial, ``Views.readRow, ``Fingerprint.sha256]

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
  return frame ["m2-reachable-v2",toString state.heap.nextRing,frame entries]

def bindingId (moduleName : Name) (name : String) : String :=
  sha256 (frame ["m2-binding-v1",nameKey moduleName,name])

def approvalPayload (theory : Theory) (id : String) (kind : Contracts.Kind)
    (fn : Value) (state : Runtime.State) : Except String String := do
  return frame [Contracts.version,id,kind.name,Contracts.render kind,theory.digest,
    ← reachable fn state]

end Macaulean.M2.Verification.Snapshot
