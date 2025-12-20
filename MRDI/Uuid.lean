import Lean.Data.Json.FromToJson


open Lean Json
--TODO decide whether to make this a structure
def Uuid := BitVec 128
  deriving Repr, BEq, Ord

instance : ToString Uuid where
  toString (u : Uuid) : String :=
    --names are from RFC 4122 and are mostly meaningless
    let timeLow := BitVec.extractLsb 127 96 u
    let timeMid := BitVec.extractLsb 95 80 u
    let timeHiAndVersion := BitVec.extractLsb 79 64 u
    let clockSeqHiAndReserved := BitVec.extractLsb 63 56 u
    let clockSeqLow := BitVec.extractLsb 55 48 u
    let node := BitVec.extractLsb 47 0 u
    s!"{timeLow.toHex}-{timeMid.toHex}-{timeHiAndVersion.toHex}-\
       {clockSeqHiAndReserved.toHex}{clockSeqLow.toHex}-{node.toHex}"

instance : ToJson Uuid where
  toJson := .str ∘ toString

def toUuid? (s : String) : Option Uuid :=
  if s.length != 36
  then .none
  else
    let parts := s.splitToList (· == '-');
    if parts.map (String.length) != [8,4,4,4,12]
    then .none
    else match parts.mapM fromHex with
      | .some [timeLow,timeMid,timeHiAndVersion,clockSeq,node] =>
        .some <|
        (timeLow : BitVec 32) ++ (timeMid : BitVec 16) ++
        (timeHiAndVersion : BitVec 16) ++
        (clockSeq : BitVec 16) ++
        (node : BitVec 48)
      | _ => .none
  where
    fromHex (s : String) : Option Nat := s.foldl (fun x c => do
      let x' ← x
      let c' ←
        if "0123456789".contains c
        then .some <| c.val - '0'.val
        else if "abcdef".contains c
        then .some <| c.val - 'a'.val + 10
        else if "ABCDEF".contains c
        then .some <| c.val - 'A'.val + 10
        else .none
      pure <| 16*x' + c'.toNat) (.some 0)

instance : FromJson Uuid where
  fromJson? (json : Json) : Except String Uuid := do
    let str : String <- fromJson? json
    match toUuid? str with
      | .some uuid => .ok uuid
      | .none => .error "Invalid UUID"

def generateUuid : IO Uuid := do
  --This consumes slightly more randomness than is optimal
  --but is conceptually simpler
  let x : BitVec 128 ← IO.rand 0 (2^128)
  let randomBits : BitVec 128 :=        0xFFFFFFFFFFFF0FFF3FFFFFFFFFFFFFFF
  let versionAndVariant : BitVec 128 := 0x00000000000040008000000000000000
  pure <| (x &&& randomBits) ||| versionAndVariant
