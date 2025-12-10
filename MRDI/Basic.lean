import Lean.Data.Json.FromToJson
open Lean Json

def Lean.githubURL := "https://github.com/leanprover/lean4"

--works for now
abbrev Uuid := String

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
  types : Std.TreeMap Uuid Type
  values : Std.DTreeMap Uuid (types.getD · Empty)

def MrdiState.empty : MrdiState := ⟨.empty,.empty⟩

class MrdiType (α : Type u) : Type _ extends ToJson α where
  mrdiType : MrdiTypeDesc
  --not using StateM because of universe issues
  decode? : Json → MrdiState → Except String α

def trivialDecode? [FromJson α] (json : Json) (_ : MrdiState) : Except String α := fromJson? json

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

--TODO FromJson instance
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
      ("_refs", toJson mrdi.refs),
      ("data", mrdi.data)
    ]

instance : FromJson Mrdi where
  fromJson? := fun
    | json@(.obj entries) => do
      -- The json schema seems to allow a file not to have a _ns parameter
      -- I don't know what we should do with that
      let .some ns := entries.get? "_ns" | .error "MRDI objects without namespaces are unspported"
      let dataPart ← fromJson? json
      let refs : Std.TreeMap Uuid MrdiData <-
        fromJson? <| entries.getD "refs" (.obj .empty)
      pure {
        toMrdiData := dataPart
        refs := refs
        ns := ns
      }
    | _ => .error "Expected an object"

def toMrdiData [MrdiType α] (x: α) : MrdiData :=
  {
    type := MrdiType.mrdiType α,
    data := toJson x
  }

def toMrdi [MrdiType α] (x: α) : Mrdi :=
  {
    toMrdiData x with
    ns := .mkObj [("Lean", .arr #[.str Lean.githubURL, .str Lean.versionString])],
    refs := .empty
  }
  -- .mkObj [("_ns", .mkObj [
  --   ("Lean", .arr #[.str Lean.githubURL, .str Lean.versionString])]),
  --   ("_type", .str $ mrdiName x),
  --   ("data", toJson x)]

-- doesn't implement references yet
def fromMrdi? [MrdiType α] (mrdi : Mrdi) : Except String α :=
  if MrdiType.mrdiType α != mrdi.type
  then .error "MRDI type does not match"
  else MrdiType.decode? mrdi.data MrdiState.empty
