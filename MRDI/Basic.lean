import Lean.Data.Json.FromToJson
open Lean Json

def Lean.githubURL := "https://github.com/leanprover/lean4"

--works for now
abbrev Uuid := String

inductive MrdiTypeDesc where
  | string : String → MrdiTypeDesc
  | parameterized : String → Json → MrdiTypeDesc
  deriving BEq

instance : ToJson MrdiTypeDesc where
  toJson := fun
    | .string s => .str s
    | .parameterized s params => .mkObj [("name", s), ("params", params)]
instance : FromJson MrdiTypeDesc where
  fromJson? := fun
    | .str s => .ok <| .string s
    | .obj terms => do
      let some nameJson := terms.get? "name" | .error "Missing name field from MRDI Type"
      let .str name := nameJson | .error "MRDI type name must be a string"
      pure <| .parameterized name (terms.getD "params" .null)
    | _ => .error "Invalid MRDI Type Descriptor"

structure MrdiData where
  type : MrdiTypeDesc
  data : Json := .null
  deriving BEq

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
  ns? : Option Json := none
  refs : Std.TreeMap Uuid Json := .empty

structure MrdiState where
  refs : Std.TreeMap Uuid Json := .empty
  resolving : List Uuid := []

def MrdiState.empty : MrdiState := ⟨.empty, []⟩

def MrdiState.withRefs (state : MrdiState) (refs : Std.TreeMap Uuid Json) : MrdiState :=
  { state with refs := refs.foldl (fun acc uuid mrdi => acc.insert uuid mrdi) state.refs }

class MrdiType (α : Type u) : Type _ extends ToJson α where
  mrdiType : MrdiTypeDesc
  decode? : MrdiData → MrdiState → Except String α

def trivialDecode? [FromJson α] (expectedType : MrdiTypeDesc)
    (mrdi : MrdiData) (_ : MrdiState) : Except String α := do
  if expectedType != mrdi.type then
    .error "MRDI type does not match"
  else
    fromJson? mrdi.data

instance : ToJson Mrdi where
  toJson mrdi :=
    let fields : List (String × Json) := [
      ("_type", toJson mrdi.type),
      ("data", mrdi.data)
    ]
    let fields :=
      match mrdi.ns? with
      | some ns => ("_ns", ns) :: fields
      | none => fields
    let fields :=
      if mrdi.refs.isEmpty then fields else ("_refs", toJson mrdi.refs) :: fields
    .mkObj fields.reverse

instance : FromJson Mrdi where
  fromJson? := fun
    | json@(.obj entries) => do
      let dataPart ← fromJson? (α := MrdiData) json
      let refs : Std.TreeMap Uuid Json <-
        fromJson? <| entries.getD "_refs" (.obj .empty)
      pure {
        toMrdiData := dataPart
        refs := refs
        ns? := entries.get? "_ns"
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
    ns? := some <| .mkObj [("Lean", .arr #[.str Lean.githubURL, .str Lean.versionString])],
    refs := .empty
  }

mutual

partial def MrdiState.resolveRef? [MrdiType α] (state : MrdiState) (uuid : Uuid) : Except String α := do
  if uuid ∈ state.resolving then
    .error s!"Cyclic MRDI reference: {uuid}"
  let some mrdiJson := state.refs.get? uuid
    | .error s!"Unknown MRDI reference: {uuid}"
  let mrdi : Mrdi ← fromJson? mrdiJson
  fromMrdiWithState? mrdi { (state.withRefs mrdi.refs) with resolving := uuid :: state.resolving }

partial def fromMrdiWithState? [MrdiType α] (mrdi : Mrdi) (state : MrdiState := .empty) : Except String α := do
  let state := state.withRefs mrdi.refs
  MrdiType.decode? { type := mrdi.type, data := mrdi.data } state

end

def MrdiState.decodeRefOrData? [MrdiType α] (state : MrdiState) (json : Json) : Except String α := do
  match json with
  | .str uuid =>
      if state.refs.contains uuid then
        state.resolveRef? uuid
      else
        .error s!"Unknown MRDI reference: {uuid}"
  | .obj _ =>
      let mrdiData ← fromJson? (α := MrdiData) json
      MrdiType.decode? mrdiData state
  | _ =>
      .error "Expected an MRDI reference string or inline MRDI data object"

def fromMrdi? [MrdiType α] (mrdi : Mrdi) : Except String α :=
  fromMrdiWithState? mrdi MrdiState.empty

instance : MrdiType Nat where
  mrdiType := .string "Lean.Nat"
  decode? := trivialDecode? (.string "Lean.Nat")

instance : MrdiType Int where
  mrdiType := .string "Lean.Int"
  decode? := trivialDecode? (.string "Lean.Int")

instance : MrdiType String where
  mrdiType := .string "Lean.String"
  decode? := trivialDecode? (.string "Lean.String")

instance : MrdiType Bool where
  mrdiType := .string "Lean.Bool"
  decode? := trivialDecode? (.string "Lean.Bool")
