import Macaulean.Verification.Contracts
import Macaulean.Verification.Fingerprint
import Lean

namespace Macaulean.M2.Verification.Tests
open Views Polynomials Lean Elab Command
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

run_cmd do
  let vectors := [
    ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    (String.ofList (List.replicate 1000 'a'), "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"),
    ("λ, 中文", "54a2a4cc2ccbb43f9428fa8f42425911df19622b47fdbc2edfb5ab62d7675185")]
  for (text, expected) in vectors do
    unless Fingerprint.sha256 text == expected do throwError "SHA-256 vector failed for {repr text}"
  unless Fingerprint.frame ["ab","c"] != Fingerprint.frame ["a","bc"] do
    throwError "ambiguous fingerprint framing"
  logInfo "INTENT_FINGERPRINTS_COMPLETE: five vectors, multi-block input and UTF-8 framing"

run_cmd do
  let r : RingInfo := ⟨0,["x","y"]⟩
  let s : RingInfo := ⟨1,["x","y"]⟩
  let raw : Raw := [(1,[1,0]),(2,[0,1]),(-1,[1,0])]
  let v : Value := .algebra (.poly r raw)
  let .ok p := readPolynomial r v | throwError "valid polynomial view rejected"
  unless p.coeff [1,0] == 0 && p.coeff [0,1] == 2 do throwError "view did not sum repeated exponents"
  unless p.raw == raw do throwError "view changed the represented coefficient data"
  unless (readPolynomial s v).isError do throwError "same-named foreign ring accepted"
  unless (readPolynomial r (.algebra (.poly r [(1,[1])]))).isError do
    throwError "malformed exponent dimension accepted"
  unless (readPolynomial r (.zz 3)).isError do throwError "scalar silently specialized as polynomial"
  unless (readRow r 2 (.list [v,v])).isOk do throwError "valid row rejected"
  unless (readRow r 1 (.list [v,v])).isError do throwError "row truncated"
  unless (readRow r 2 (.list [v,.algebra (.poly s raw)])).isError do throwError "foreign row entry accepted"
  unless (readRow r 0 (.list [])).isOk do throwError "empty row rejected"
  for kind in Contracts.all do
    unless (Contracts.Kind.parse kind.name) == some kind do throwError "schema name did not round trip"
    unless (Contracts.describe kind).limitations.length == 4 do throwError "a contract lost explicit boundaries"
  unless Contracts.Kind.parse "arbitraryPredicate" == none do throwError "unknown schema accepted"
  logInfo "INTENT_VIEWS_COMPLETE: dimensions, duplicates, ring identity and explicit schema boundaries"

example : coefficient [(1,[1]),(2,[1])] [1] = 3 := by decide +kernel
example : coefficient [(1,[1]),(-1,[1])] [1] = 0 := by decide +kernel

end Macaulean.M2.Verification.Tests
