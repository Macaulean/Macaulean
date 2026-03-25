import MRDI.Poly

open Lean Json

namespace MacauleanTest.MRDI

def parameterizedDesc : MrdiTypeDesc :=
  .parameterized "Example"
    (.mkObj [("arity", toJson (2 : Nat)), ("coeff", .str "QQ")])

example : (fromJson? (α := MrdiTypeDesc) (toJson parameterizedDesc)) = .ok parameterizedDesc := rfl

def minimalPolyJson : Json :=
  .mkObj [
    ("_type", toJson (MrdiTypeDesc.string "Lean.Grind.CommRing.Poly")),
    ("data", toJson MRDI.test.data)
  ]

def decodedMinimalPoly : Except String MRDI.Poly := do
  let mrdi : Mrdi ← fromJson? minimalPolyJson
  fromMrdi? mrdi

def decodedMinimalPolyOk : Bool :=
  match decodedMinimalPoly with
  | .ok poly => poly == MRDI.test
  | .error _ => false

#guard decodedMinimalPolyOk

structure PolyRef where
  poly : MRDI.Poly
  deriving Repr, DecidableEq

instance : ToJson PolyRef where
  toJson x := .mkObj [("poly", toJson x.poly)]

instance : MrdiType PolyRef where
  mrdiType := .string "MacauleanTest.PolyRef"
  decode? mrdi state := do
    if mrdi.type != .string "MacauleanTest.PolyRef" then
      .error "MRDI type does not match"
    let .obj entries := mrdi.data | .error "Expected object payload"
    let some polyJson := entries.get? "poly" | .error "Missing poly field"
    let poly ← state.decodeRefOrData? (α := MRDI.Poly) polyJson
    pure { poly }

def refUuid : Uuid := "123e4567-e89b-12d3-a456-426614174000"

def referencedPoly : Json := toJson <| toMrdi MRDI.test

def refPayload : Mrdi :=
  { type := .string "MacauleanTest.PolyRef"
    data := .mkObj [("poly", .str refUuid)]
    refs := (Std.TreeMap.empty.insert refUuid referencedPoly : Std.TreeMap Uuid Json) }

def decodedPolyRef : Except String PolyRef := fromMrdi? refPayload

def decodedPolyRefOk : Bool :=
  match decodedPolyRef with
  | .ok polyRef => polyRef.poly == MRDI.test
  | .error _ => false

#guard decodedPolyRefOk

end MacauleanTest.MRDI
