import Lean.Data.Json.FromToJson
open Lean Json

def Lean.githubURL := "https://github.com/leanprover/lean4"

--This is enough of a skeleton to transfer Mrdi data, but isn't a correct implementation, because the class
--MrdiType isn't sufficiently general. In particular, it can't deal with anything that needs
--references to other objects

--works for now
abbrev Uuid := String

inductive MrdiTypeDesc where
  | string : String → MrdiTypeDesc
  | parameterized : String → List Uuid → MrdiTypeDesc
  deriving Repr

instance : ToJson MrdiTypeDesc where
  toJson := fun
    | .string s => .str s
    | .parameterized s uuids => .mkObj [("name", s), ("params", toJson uuids)]
instance : FromJson MrdiTypeDesc where
  fromJson? := fun
    | .str s => .ok <| .string s
    | .obj terms => sorry
    | _ => .error "Invalid MRDI Type Descriptor"

class MrdiType (α : Type u) : Type u extends ToJson α, FromJson α where
  mrdiType : MrdiTypeDesc

--TODO From/ToJson instances
structure MrdiData where
  type : MrdiTypeDesc
  data : Json

instance : ToJson MrdiData where
  toJson data :=
    .mkObj [
      ("_type", toJson data.type),
      ("data", data.data)
    ]

--TODO From/ToJson instances
structure Mrdi extends MrdiData where
  ns : Json
  refs : Std.TreeMap Uuid MrdiData
  deriving ToJson

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

def fromMrdi [MrdiType α] (mrdi : Mrdi) : α := sorry
