import Lean

/-!
# Proof terms as data

The independent checker reads this format, not Lean source supplied by a worker.
No macros, tactics, free variables, metavariables, callbacks or declarations can
be encoded. Child indices must precede their parents. Kernel checking remains
mandatory: decoding is not evidence of well-typedness.
-/
namespace Macaulean.M2.Verification.ProofData
open Lean

def nameJson : Name → Json
  | .anonymous => toJson ([] : List Json)
  | .str p s => toJson [Json.str "s", nameJson p, Json.str s]
  | .num p n => toJson [Json.str "n", nameJson p, toJson n]

def readName : Nat → Json → Except String Name
  | 0, _ => .error "proof name exceeds depth limit"
  | fuel+1, j => do
    match (← j.getArr?).toList with
    | [] => return .anonymous
    | [Json.str "s", p, Json.str s] => return .str (← readName fuel p) s
    | [Json.str "n", p, n] => return .num (← readName fuel p) (← n.getNat?)
    | _ => .error "invalid proof name"

def levelJson : Level → Except String Json
  | .zero => return toJson [Json.str "z"]
  | .succ u => return toJson [Json.str "s", ← levelJson u]
  | .max u v => return toJson [Json.str "max", ← levelJson u, ← levelJson v]
  | .imax u v => return toJson [Json.str "imax", ← levelJson u, ← levelJson v]
  | .param n => return toJson [Json.str "p", nameJson n]
  | .mvar _ => .error "unresolved universe metavariable in proof"

def readLevel : Nat → Json → Except String Level
  | 0, _ => .error "proof universe exceeds depth limit"
  | fuel+1, j => do
    match (← j.getArr?).toList with
    | [Json.str "z"] => return .zero
    | [Json.str "s", u] => return .succ (← readLevel fuel u)
    | [Json.str "max", u, v] => return .max (← readLevel fuel u) (← readLevel fuel v)
    | [Json.str "imax", u, v] => return .imax (← readLevel fuel u) (← readLevel fuel v)
    | [Json.str "p", n] => return .param (← readName fuel n)
    | _ => .error "invalid proof universe"

def binderJson : BinderInfo → Json
  | .default => Json.str "explicit"
  | .implicit => Json.str "implicit"
  | .strictImplicit => Json.str "strictImplicit"
  | .instImplicit => Json.str "instance"

def readBinder : Json → Except String BinderInfo
  | Json.str "explicit" => .ok .default
  | Json.str "implicit" => .ok .implicit
  | Json.str "strictImplicit" => .ok .strictImplicit
  | Json.str "instance" => .ok .instImplicit
  | _ => .error "invalid proof binder"

structure EncodeState where
  nodes : Array Json := #[]
  seen : Std.HashMap Expr Nat := {}

private def encodeExpr (e : Expr) : StateT EncodeState (Except String) Nat := do
  if let some i := (← get).seen[e]? then return i
  let data ← match e with
    | .bvar i => pure [Json.str "bvar", toJson i]
    | .const n us => do
      let us ← liftM (us.mapM levelJson)
      pure [Json.str "const", nameJson n, toJson us]
    | .sort u => pure [Json.str "sort", ← levelJson u]
    | .app f a => pure [Json.str "app", toJson (← encodeExpr f), toJson (← encodeExpr a)]
    | .lam n t b bi => pure [Json.str "lam", nameJson n, toJson (← encodeExpr t),
        toJson (← encodeExpr b), binderJson bi]
    | .forallE n t b bi => pure [Json.str "forall", nameJson n, toJson (← encodeExpr t),
        toJson (← encodeExpr b), binderJson bi]
    | .letE n t v b nondep => pure [Json.str "let", nameJson n, toJson (← encodeExpr t),
        toJson (← encodeExpr v), toJson (← encodeExpr b), toJson nondep]
    | .lit (.natVal n) => pure [Json.str "nat", toJson n]
    | .lit (.strVal s) => pure [Json.str "str", Json.str s]
    | .proj n i a => pure [Json.str "proj", nameJson n, toJson i, toJson (← encodeExpr a)]
    | .mdata _ a => return ← encodeExpr a
    | .fvar _ => throw "free variable in transported proof"
    | .mvar _ => throw "unresolved metavariable in transported proof"
  let i := (← get).nodes.size
  modify fun s => { nodes := s.nodes.push (toJson data), seen := s.seen.insert e i }
  return i
termination_by structural e

def encode (e : Expr) : Except String Json := do
  let (root,s) ← (encodeExpr e).run {}
  return Json.mkObj [("format", Json.str "macaulean.proof-term.v1"),
    ("nodes", toJson s.nodes), ("root", toJson root)]

private def child (nodes : Array Expr) (j : Json) : Except String Expr := do
  let i ← j.getNat?
  let some e := nodes[i]? | .error "proof child index is not a preceding node"
  return e

private def readNode (nodes : Array Expr) (j : Json) : Except String Expr := do
  match (← j.getArr?).toList with
  | [Json.str "bvar", i] => return .bvar (← i.getNat?)
  | [Json.str "const", n, us] =>
    return .const (← readName 1024 n) (← (← us.getArr?).toList.mapM (readLevel 1024))
  | [Json.str "sort", u] => return .sort (← readLevel 1024 u)
  | [Json.str "app", f, a] => return .app (← child nodes f) (← child nodes a)
  | [Json.str "lam", n, t, b, bi] =>
    return .lam (← readName 1024 n) (← child nodes t) (← child nodes b) (← readBinder bi)
  | [Json.str "forall", n, t, b, bi] =>
    return .forallE (← readName 1024 n) (← child nodes t) (← child nodes b) (← readBinder bi)
  | [Json.str "let", n, t, v, b, nondep] =>
    return .letE (← readName 1024 n) (← child nodes t) (← child nodes v)
      (← child nodes b) (← nondep.getBool?)
  | [Json.str "nat", n] => return .lit (.natVal (← n.getNat?))
  | [Json.str "str", Json.str s] => return .lit (.strVal s)
  | [Json.str "proj", n, i, a] =>
    return .proj (← readName 1024 n) (← i.getNat?) (← child nodes a)
  | _ => .error "unsupported or malformed proof node"

def decode (j : Json) (maxNodes : Nat := 200000) : Except String Expr := do
  unless (← j.getObjValAs? String "format") == "macaulean.proof-term.v1" do
    .error "unknown proof term format"
  let data ← j.getObjValAs? (Array Json) "nodes"
  unless data.size > 0 && data.size ≤ maxNodes do .error "proof node budget exceeded or empty proof"
  let mut nodes : Array Expr := #[]
  for node in data do nodes := nodes.push (← readNode nodes node)
  let root ← j.getObjValAs? Nat "root"
  unless root + 1 == nodes.size do .error "proof root must be the last node"
  let e := nodes[root]!
  if e.hasLooseBVars || e.hasFVar || e.hasMVar then .error "proof term is not closed"
  else return e

end Macaulean.M2.Verification.ProofData
