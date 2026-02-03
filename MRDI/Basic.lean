import Lean.Data.Json.FromToJson
import MRDI.Uuid
open Lean Json

def Lean.githubURL := "https://github.com/leanprover/lean4"

inductive MrdiTypeDesc where
  | string : String → MrdiTypeDesc
  | parameterized : String → Json → MrdiTypeDesc
  deriving BEq

instance : ToString MrdiTypeDesc where
  toString := fun
    | .string s => s
    | .parameterized s param => s ++ "{" ++ toString param ++ "}"

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
  randomGen : StdGen
  values : Std.TreeMap Uuid Dynamic
  uuids : Std.TreeMap USize Uuid
  --^ I don't know that this is quite right, in particular, I think two objects with different types can have the same address when you use subtypes

--TODO do a better job seeding the random number generator
def MrdiState.empty : MrdiState := ⟨mkStdGen, .empty, .empty⟩

unsafe def MrdiState.addEntry [TypeName α] (state : MrdiState) (u : Uuid) (x : α) : MrdiState :=
  { state with
    values := state.values.insert u (Dynamic.mk x)
    uuids := state.uuids.insert (ptrAddrUnsafe x) u
  }

/--
Tries to get the entry corresponding to the given Uuid, given a proof that it is in the table.
Returns none if the value isn't of type α
-/
def MrdiState.getEntry [TypeName α] (state : MrdiState) (u : Uuid) (h : u ∈ state.values) : Option α :=
  (state.values.get u h).get? α

def MrdiState.getEntry? [TypeName α] (state : MrdiState) (u : Uuid) : Option α := do
  let v ← state.values.get? u
  v.get? α

unsafe def MrdiState.getUuid (state : MrdiState) (x : α) : Option Uuid :=
  state.uuids.get? (ptrAddrUnsafe x)

abbrev MrdiT := StateT MrdiState
abbrev MrdiM := StateM MrdiState

def genUuid [MonadState MrdiState m] : m Uuid :=
  modifyGet <| fun s =>
    let (x, g) := randUuid s.randomGen
    (x, {s with randomGen := g})

unsafe def insertEntry [Monad m] [MonadStateOf MrdiState m] [TypeName α] (x : α) : m (Uuid) := do
  let optUuid := (← get).getUuid x
  let uuid := optUuid.getD (← genUuid)
  modify (fun s => s.addEntry uuid x)
  pure uuid

structure MrdiData where
  type : MrdiTypeDesc
  data : Json

structure Mrdi extends MrdiData where
  ns : Json
  refs : Std.TreeMap Uuid MrdiData

/-
TODO consider if the extends MrdiState is overcomplicating things
-/
structure MrdiEncodeState extends MrdiState where
  currentReferences : Std.TreeMap Uuid MrdiData

/--
This monad is used to implement encode, and stores information about the current object
being encoded, and in partcular, what references have been encoded
-/
abbrev MrdiEncodeT := StateT MrdiEncodeState
abbrev MrdiEncodeM := StateM MrdiEncodeState

instance (priority := mid) [Monad m] : MonadStateOf MrdiState (MrdiEncodeT m) where
  get := MrdiEncodeState.toMrdiState <$> get
  set (s : MrdiState) := modify (fun s' => {s' with toMrdiState := s})
  modifyGet f := modifyGet (fun s =>
    let (x,s') := f (s.toMrdiState)
    (x,{s with toMrdiState := s'}))

instance [Monad m] [MonadState MrdiState m] : MonadLift MrdiM m where
  monadLift act := modifyGet act.run

/-
  TODO consider whether to rewrite decode? and encode back to being simple functions
-/
class MrdiType α where
  mrdiType : MrdiTypeDesc
  decode? : Json → MrdiM (Except String α)
  /--
  Return only the JSON that gives the data field.
  -/
  encode: α → MrdiEncodeM Json

def trivialDecode? [FromJson α] (json : Json) : MrdiM (Except String α) := pure <| fromJson? json
def trivialEncode [ToJson α] (x : α) : MrdiEncodeT Id Json := pure <| toJson x

def toMrdiData [Monad m] [MrdiType α] (x: α) : MrdiEncodeT m MrdiData := do
  let jsonData ← modifyGet <| MrdiType.encode x
  pure {
    type := MrdiType.mrdiType α
    data := jsonData
  }

def runEncode [Monad m] (ns: Json) (act : MrdiEncodeT m MrdiData) : MrdiT m Mrdi := do
  let (data, s) ← act.run {toMrdiState := (← get), currentReferences := .empty}
  set s.toMrdiState
  pure {
    toMrdiData := data
    ns := ns
    refs := s.currentReferences
  }

def toMrdi [Monad m] [MrdiType α] (x: α) : MrdiT m Mrdi :=
  runEncode ns (toMrdiData x)
  where
    ns := .mkObj [("Lean", .arr #[.str Lean.githubURL, .str Lean.versionString])]

--- Either calls encode and stores it in the reference table or looks it up in the reference table
unsafe def addReference [Monad m] [TypeName α] [MrdiType α] (x : α) : MrdiEncodeT m Uuid := do
  let uuid ← insertEntry x
  if !(← get).currentReferences.contains uuid
  then
    let data ← toMrdiData x
    modify (fun s => {s with currentReferences := s.currentReferences.insert uuid data})
  pure uuid

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

-- doesn't implement references yet
def fromMrdi? [Monad m] [MrdiType α] (mrdi : Mrdi) : MrdiT m (Except String α) :=
  if MrdiType.mrdiType α != mrdi.type
  then pure <| .error "MRDI type does not match"
  else MrdiType.decode? mrdi.data
