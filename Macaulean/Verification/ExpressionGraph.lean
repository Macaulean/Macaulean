import Lean
import Macaulean.Verification.Fingerprint

/-!
# Canonical expression graphs

Generated Lean declarations share subexpressions heavily. Expanding that DAG into
an ordinary tree can exhaust memory before a developer can review a contract.
This encoding interns exact constructor records with child indices. Hash-map
collisions are resolved by structural/string equality, never treated as identity.
Binder names and metadata are erased deliberately; bound indices, binder modes,
constants, universes, literals, projections and let flags are retained.
-/
namespace Macaulean.M2.Verification.ExpressionGraph
open Lean Fingerprint

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

structure Graph where
  visited : ExprStructMap Nat := {}
  interned : Std.HashMap String Nat := {}
  nodes : Array String := #[]
  constants : NameSet := {}
  deriving Inhabited

private def intern (record : String) : StateM Graph Nat := do
  let graph ← get
  if let some id := graph.interned[record]? then return id
  let id := graph.nodes.size
  set { graph with nodes := graph.nodes.push record, interned := graph.interned.insert record id }
  return id

/-- Each subexpression is encoded once. Interning the resulting constructor record
also identifies alpha-equivalent nodes independently of sharing in the input. -/
def encode (e : Expr) : StateM Graph Nat := do
  if let some id := (← get).visited.get? e then return id
  let id ← match e with
    | .mdata _ child => encode child
    | .bvar i => intern (frame ["bvar",toString i])
    | .fvar i => intern (frame ["fvar",nameKey i.name])
    | .mvar i => intern (frame ["mvar",nameKey i.name])
    | .sort u => intern (frame ["sort",levelKey u])
    | .const n us => do
      modify fun graph => { graph with constants := graph.constants.insert n }
      intern (frame ["const",nameKey n,frame (us.map levelKey)])
    | .app f a => do
      let f ← encode f
      let a ← encode a
      intern (frame ["app",toString f,toString a])
    | .lam _ t b bi => do
      let t ← encode t
      let b ← encode b
      intern (frame ["lam",binderKey bi,toString t,toString b])
    | .forallE _ t b bi => do
      let t ← encode t
      let b ← encode b
      intern (frame ["forall",binderKey bi,toString t,toString b])
    | .letE _ t v b nondep => do
      let t ← encode t
      let v ← encode v
      let b ← encode b
      intern (frame ["let",toString nondep,toString t,toString v,toString b])
    | .lit (.natVal n) => intern (frame ["nat",toString n])
    | .lit (.strVal s) => intern (frame ["string",s])
    | .proj n i child => do
      modify fun graph => { graph with constants := graph.constants.insert n }
      let child ← encode child
      intern (frame ["proj",nameKey n,toString i,toString child])
  modify fun graph => { graph with visited := graph.visited.insert e id }
  return id
termination_by structural e

structure Encoded where
  payload : String
  constants : List Name
  nodeCount : Nat

def encodeMany (expressions : List Expr) : Encoded :=
  let (roots, graph) := (expressions.mapM encode).run {}
  { payload := frame ["lean-expr-dag-v1",frame (roots.map toString),frame graph.nodes.toList]
    constants := graph.constants.toArray.toList
    nodeCount := graph.nodes.size }

def key (e : Expr) : String := (encodeMany [e]).payload

end Macaulean.M2.Verification.ExpressionGraph
