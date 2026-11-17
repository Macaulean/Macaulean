import Lean

/-!
A deliberately small wire format for *closed kernel expressions*. No tactic,
parser extension, command, external process, environment mutation, free variable,
or metavariable is represented by this format. Decoding is bounded and every
constructor has an exact arity. Name components are retained, not joined/split on
periods. The accepting side still kernel-checks the decoded expression.
-/
namespace Macaulean.M2.Verification.ProofJobs.Wire
open Lean

def arr (xs : List Json) : Json := Json.arr xs.toArray

def nameToJson : Name → Json
  | .anonymous => arr [toJson (0 : Nat)]
  | .str parent text => arr [toJson (1 : Nat), nameToJson parent, toJson text]
  | .num parent number => arr [toJson (2 : Nat), nameToJson parent, toJson number]

def nameFromJson : Nat → Json → Except String Name
  | 0, _ => .error "proof wire: name depth exceeded"
  | fuel+1, j => do
    match (← j.getArr?).toList with
    | [tag] => if (← tag.getNat?) == 0 then return .anonymous else .error "invalid name tag"
    | [tag,parent,text] =>
      match ← tag.getNat? with
      | 1 => return .str (← nameFromJson fuel parent) (← text.getStr?)
      | 2 => return .num (← nameFromJson fuel parent) (← text.getNat?)
      | _ => .error "invalid name tag"
    | _ => .error "invalid name constructor arity"

def levelToJson : Level → Except String Json
  | .zero => do return arr [toJson (0 : Nat)]
  | .succ a => do return arr [toJson (1 : Nat), ← levelToJson a]
  | .max a b => do return arr [toJson (2 : Nat), ← levelToJson a, ← levelToJson b]
  | .imax a b => do return arr [toJson (3 : Nat), ← levelToJson a, ← levelToJson b]
  | .param n => do return arr [toJson (4 : Nat), nameToJson n]
  | .mvar _ => .error "proof wire: unresolved universe metavariable"

def levelFromJson : Nat → Json → Except String Level
  | 0, _ => .error "proof wire: universe depth exceeded"
  | fuel+1, j => do
    match (← j.getArr?).toList with
    | [tag] => if (← tag.getNat?) == 0 then return .zero else .error "invalid level tag"
    | [tag,a] =>
      match ← tag.getNat? with
      | 1 => return .succ (← levelFromJson fuel a)
      | 4 => return .param (← nameFromJson fuel a)
      | _ => .error "invalid level tag"
    | [tag,a,b] =>
      match ← tag.getNat? with
      | 2 => return .max (← levelFromJson fuel a) (← levelFromJson fuel b)
      | 3 => return .imax (← levelFromJson fuel a) (← levelFromJson fuel b)
      | _ => .error "invalid level tag"
    | _ => .error "invalid universe constructor arity"

def binderToNat : BinderInfo → Nat
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

def binderFromNat : Nat → Except String BinderInfo
  | 0 => do return .default | 1 => do return .implicit
  | 2 => do return .strictImplicit | 3 => do return .instImplicit
  | _ => .error "proof wire: invalid binder mode"

def encode : Expr → Except String Json
  | .bvar n => do return arr [toJson (0 : Nat), toJson n]
  | .sort u => do return arr [toJson (1 : Nat), ← levelToJson u]
  | .const name levels => do return arr [toJson (2 : Nat), nameToJson name,
      arr (← levels.mapM levelToJson)]
  | .app f a => do return arr [toJson (3 : Nat), ← encode f, ← encode a]
  | .lam n t b mode => do return arr [toJson (4 : Nat), nameToJson n,
      ← encode t, ← encode b, toJson (binderToNat mode)]
  | .forallE n t b mode => do return arr [toJson (5 : Nat), nameToJson n,
      ← encode t, ← encode b, toJson (binderToNat mode)]
  | .letE n t v b nondep => do return arr [toJson (6 : Nat), nameToJson n,
      ← encode t, ← encode v, ← encode b, toJson nondep]
  | .lit (.natVal n) => do return arr [toJson (7 : Nat), toJson n]
  | .lit (.strVal s) => do return arr [toJson (8 : Nat), toJson s]
  | .proj n i e => do return arr [toJson (9 : Nat), nameToJson n, toJson i, ← encode e]
  | .mdata _ e => encode e
  | .fvar _ => .error "proof wire: free variable"
  | .mvar _ => .error "proof wire: unresolved metavariable"

def decode : Nat → Json → Except String Expr
  | 0, _ => .error "proof wire: expression depth exceeded"
  | fuel+1, j => do
    let fields ← j.getArr?
    let some tag := fields[0]? | .error "proof wire: empty expression"
    match (← tag.getNat?), fields.toList.drop 1 with
    | 0, [n] => return .bvar (← n.getNat?)
    | 1, [u] => return .sort (← levelFromJson fuel u)
    | 2, [n,us] => return .const (← nameFromJson fuel n) (← (← us.getArr?).toList.mapM (levelFromJson fuel))
    | 3, [f,a] => return .app (← decode fuel f) (← decode fuel a)
    | 4, [n,t,b,mode] => return .lam (← nameFromJson fuel n) (← decode fuel t) (← decode fuel b) (← binderFromNat (← mode.getNat?))
    | 5, [n,t,b,mode] => return .forallE (← nameFromJson fuel n) (← decode fuel t) (← decode fuel b) (← binderFromNat (← mode.getNat?))
    | 6, [n,t,v,b,nondep] => return .letE (← nameFromJson fuel n) (← decode fuel t) (← decode fuel v) (← decode fuel b) (← nondep.getBool?)
    | 7, [n] => return .lit (.natVal (← n.getNat?))
    | 8, [s] => return .lit (.strVal (← s.getStr?))
    | 9, [n,i,e] => return .proj (← nameFromJson fuel n) (← i.getNat?) (← decode fuel e)
    | _, _ => .error "proof wire: unknown expression tag or wrong arity"

end Macaulean.M2.Verification.ProofJobs.Wire
