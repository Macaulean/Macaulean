import Lean.Data.Json.FromToJson
import MRDI.Uuid
open Lean Json

def Lean.githubURL := "https://github.com/leanprover/lean4"

inductive MrdiTypeDesc where
  | string : String → MrdiTypeDesc
  | parameterized : String → List Uuid → MrdiTypeDesc
  deriving Repr,BEq,Ord

instance : ToJson MrdiTypeDesc where
  toJson := fun
    | .string s => .str s
    | .parameterized s uuids => .mkObj [("name", s), ("params", toJson uuids)]
instance : FromJson MrdiTypeDesc where
  fromJson? := fun
    | .str s => .ok <| .string s
    | .obj terms =>  .parameterized
      <$> (terms.get? "name").elim (.error "Missing name field from MRDI Type") fromJson?
      <*> (terms.get? "params").elim (.error "Missing params field from MRDI Type") fromJson?
    | _ => .error "Invalid MRDI Type Descriptor"


structure MrdiState where
  values : Std.TreeMap Uuid Dynamic
  uuids : Std.TreeMap USize Uuid
  --^ I don't know that this is quite right, in particular, I think two objects with different types can have the same address when you use subtypes

def MrdiState.empty : MrdiState := ⟨.empty, .empty⟩

unsafe def MrdiState.addEntry [TypeName α] (state : MrdiState) (u : Uuid) (x : α) : MrdiState :=
  ⟨state.values.insert u (Dynamic.mk x), state.uuids.insert (ptrAddrUnsafe x) u⟩

def MrdiState.getEntry [TypeName α] (state : MrdiState) (u : Uuid) (h : u ∈ state.values) : Option α :=
  (state.values.get u h).get? α

def MrdiState.getEntry? [TypeName α] (state : MrdiState) (u : Uuid) : Option α := do
  let v ← state.values.get? u
  v.get? α

unsafe def MrdiState.getUuid (state : MrdiState) (x : α) : Option Uuid :=
  state.uuids.get? (ptrAddrUnsafe x)

abbrev MrdiT := StateT MrdiState
abbrev MrdiM := StateM MrdiState

instance [Monad m] [MonadState MrdiState m] : MonadLift MrdiM m where
  monadLift act := modifyGet act.run

/-
  TODO consider whether to rewrite decode? and encode back to being simple functions
-/
class MrdiType α where
  mrdiType : MrdiTypeDesc
  decode? : Json → MrdiM (Except String α)
  encode: α → MrdiM Json

def trivialDecode? [FromJson α] (json : Json) : MrdiM (Except String α) := pure <| fromJson? json
def trivialEncode [ToJson α] (x : α) : MrdiM Json := pure <| toJson x

structure MrdiData where
  type : MrdiTypeDesc
  data : Json

instance : ToJson MrdiData where
  toJson data :=
    .mkObj [
      ("_type", toJson data.type),
      ("data", data.data)
    ]

instance : FromJson MrdiData where
  fromJson? := fun
    | .obj entries => do
      let .some type := entries.get? "_type" | .error "MRDI objects must contain a _type field"
      let mrdiType <- fromJson? type
      pure {
        type := mrdiType
        data := entries.getD "data" .null
        }
    | _ => .error "Expected an object"

structure Mrdi extends MrdiData where
  ns : Json
  refs : Std.TreeMap Uuid MrdiData

instance : ToJson Mrdi where
  toJson mrdi :=
    if mrdi.refs.isEmpty
    then .mkObj [
      ("_ns", mrdi.ns),
      ("_type", toJson mrdi.type),
      ("data", mrdi.data)
    ]
    else .mkObj [
      ("_ns", mrdi.ns),
      ("_type", toJson mrdi.type),
      ("_refs", toJson <| Std.TreeMap.ofArray <| (fun (k,v) => (toString k, v)) <$> mrdi.refs.toArray ),
      ("data", mrdi.data)
    ]

instance : FromJson Mrdi where
  fromJson? := fun
    | json@(.obj entries) => do
      -- The json schema seems to allow a file not to have a _ns parameter
      -- I don't know what we should do with that
      let .some ns := entries.get? "_ns" | .error "MRDI objects without namespaces are unspported"
      let dataPart ← fromJson? json
      let refs : Std.TreeMap String MrdiData ←
        fromJson? <| entries.getD "refs" (.obj .empty)
      let parsedRefs : Std.TreeMap Uuid MrdiData  ←
        .ofArray (cmp := Ord.compare) <$>
        refs.toArray.mapM (fun (k,v) =>
          match toUuid? k with
            | .some u => .ok (u,v)
            | .none => .error "Invalid UUID")
      pure {
        toMrdiData := dataPart
        refs := parsedRefs
        ns := ns
      }
    | _ => .error "Expected an object"

def toMrdiData [Monad m] [MrdiType α] (x: α) : MrdiT m MrdiData := do
  let jsonData ← MrdiType.encode x
  pure {
    type := MrdiType.mrdiType α
    data := jsonData
  }

def toMrdi [Monad m] [MrdiType α] (x: α) : MrdiT m Mrdi := do
  pure {
    ← toMrdiData x with
    ns := .mkObj [("Lean", .arr #[.str Lean.githubURL, .str Lean.versionString])],
    refs := .empty
  }

-- doesn't implement references yet
def fromMrdi? [Monad m] [MrdiType α] (mrdi : Mrdi) : MrdiT m (Except String α) :=
  if MrdiType.mrdiType α != mrdi.type
  then pure <| .error "MRDI type does not match"
  else MrdiType.decode? mrdi.data
