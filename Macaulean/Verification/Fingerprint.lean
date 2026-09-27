import Lean

/-!
# Approval fingerprints

SHA-256 labels canonical length-framed data. It is an integrity fingerprint, not
a signature or human authentication. Live records retain exact payloads. Source
attestations and declaration manifests rely on SHA-256 collision resistance.
-/
namespace Macaulean.M2.Verification.Fingerprint

def frame (parts : List String) : String :=
  String.join (parts.map fun s => toString s.utf8ByteSize ++ ":" ++ s)

private def initial : Array UInt32 := #[
  0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
  0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]
private def constants : Array UInt32 := #[
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]
private def rotate (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32-n))
private def small0 (x : UInt32) := rotate x 7 ^^^ rotate x 18 ^^^ (x >>> 3)
private def small1 (x : UInt32) := rotate x 17 ^^^ rotate x 19 ^^^ (x >>> 10)
private def big0 (x : UInt32) := rotate x 2 ^^^ rotate x 13 ^^^ rotate x 22
private def big1 (x : UInt32) := rotate x 6 ^^^ rotate x 11 ^^^ rotate x 25

private def compress (state : Array UInt32) (bytes : Array UInt8) (offset : Nat) : Array UInt32 := Id.run do
  let mut words : Array UInt32 := #[]
  for i in [0:16] do
    let j := offset+4*i
    let w := bytes[j]!.toUInt32 <<< 24 ||| bytes[j+1]!.toUInt32 <<< 16 |||
      bytes[j+2]!.toUInt32 <<< 8 ||| bytes[j+3]!.toUInt32
    words := words.push w
  for i in [16:64] do
    words := words.push (small1 words[i-2]! + words[i-7]! + small0 words[i-15]! + words[i-16]!)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let choose := (e &&& f) ^^^ ((~~~e) &&& g)
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t1 := h + big1 e + choose + constants[i]! + words[i]!
    let t2 := big0 a + majority
    h := g
    g := f
    f := e
    e := d+t1
    d := c
    c := b
    b := a
    a := t1+t2
  return #[state[0]!+a,state[1]!+b,state[2]!+c,state[3]!+d,
    state[4]!+e,state[5]!+f,state[6]!+g,state[7]!+h]

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat+n else 'a'.toNat+(n-10))
private def wordHex (w : UInt32) : String :=
  String.ofList ((List.range 8).map fun i => hexDigit ((w.toNat >>> (4*(7-i))) % 16))

/-- Iterate directly over padded bytes; no recursive copying of the message. -/
def sha256 (source : String) : String := Id.run do
  let mut bytes := source.toUTF8.data
  let bits := bytes.size*8
  let padding := (64 - ((bytes.size+9)%64))%64
  bytes := bytes.push 128
  for _ in [0:padding] do bytes := bytes.push 0
  for i in [0:8] do bytes := bytes.push (UInt8.ofNat ((bits >>> (8*(7-i)))%256))
  let mut state := initial
  for block in [0:bytes.size/64] do state := compress state bytes (64*block)
  return String.join (state.toList.map wordHex)

end Macaulean.M2.Verification.Fingerprint
