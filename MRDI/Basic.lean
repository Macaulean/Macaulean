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

abbrev AnyValue.{u} := (α : Type u) × α

def AnyValue.type (v : AnyValue) : Type _ := v.1
def AnyValue.value (v : AnyValue) : v.1 := v.2

structure MrdiState where
  values : Std.TreeMap Uuid AnyValue
  uuids : Std.TreeMap USize Uuid
  --^ I don't know that this is quite right, in particular, I think two objects with different types can have the same address when you use subtypes

def MrdiState.empty : MrdiState := ⟨.empty, .empty⟩

unsafe def MrdiState.addEntry (state : MrdiState) (u : Uuid) (x : α) : MrdiState :=
  ⟨state.values.insert u ⟨α, x⟩, state.uuids.insert (ptrAddrUnsafe x) u⟩

def MrdiState.getEntry (state : MrdiState) (u : Uuid) (h : u ∈ state.values) : (state.values.get u h).1 :=
  (state.values.get u h).2

--exploits the fact that it's impossible to have inserted a value of Type Empty
def MrdiState.getType (state : MrdiState) (u : Uuid) : Type :=
  match (state.values.get? u) with
    | .some ⟨t, _⟩ => t
    | .none => Empty

def MrdiState.getEntry? (state : MrdiState) (u : Uuid) : Option (state.getType u) :=
  let optV := state.values.get? u
  match h : optV with
    | .some ⟨t, v⟩ =>
        let h : t = state.getType u := by
          let p : AnyValue := ⟨t, v⟩
          unfold MrdiState.getType
          subst optV
          simp [h]
        Option.some (cast h <| v)
    | .none => .none

unsafe def MrdiState.getUuid (state : MrdiState) (x : α) : Option Uuid :=
  state.uuids.get? (ptrAddrUnsafe x)

structure MrdiT (m : Type _ → Type v) α where
  runMrdi : MrdiState → m (α × MrdiState)

abbrev MrdiM := MrdiT Id

instance [Monad m] : Monad (MrdiT m) where
  pure x := {runMrdi := fun s => pure (x,s)}
  bind p f := {runMrdi := fun s => do
    let (x,s') ← p.runMrdi s
    (f x).runMrdi s'
    }

-- Explicitly specified universes to avoid
-- being too universe polymorphic
class MrdiType.{u} (α : Type u) : Type _ where
  mrdiType : MrdiTypeDesc
  --not using StateM because of universe issues
  decode? : Json → MrdiState.{u} → Except String α
  encode : α → MrdiState.{u} → Json × MrdiState.{u}

def trivialDecode? [FromJson α] (json : Json) (_ : MrdiState) : Except String α := fromJson? json
def trivialEncode [ToJson α] (x : α) (_ : MrdiState) : Json × MrdiState := ⟨toJson x, .empty⟩

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

def toMrdiData [MrdiType α] (x: α) : MrdiData :=
  {
    type := MrdiType.mrdiType α,
    data := (MrdiType.encode x .empty).1
  }

def toMrdi [MrdiType α] (x: α) : Mrdi :=
  {
    toMrdiData x with
    ns := .mkObj [("Lean", .arr #[.str Lean.githubURL, .str Lean.versionString])],
    refs := .empty
  }

-- doesn't implement references yet
def fromMrdi? [MrdiType α] (mrdi : Mrdi) : Except String α :=
  if MrdiType.mrdiType α != mrdi.type
  then .error "MRDI type does not match"
  else MrdiType.decode? mrdi.data MrdiState.empty
