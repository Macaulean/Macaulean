import Macaulean.Verification.Contracts
import Macaulean.Verification.ViewLaws
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
  if (readPolynomial s v).isOk then throwError "same-named foreign ring accepted"
  if (readPolynomial r (.algebra (.poly r [(1,[1])]))).isOk then
    throwError "malformed exponent dimension accepted"
  if (readPolynomial r (.zz 3)).isOk then throwError "scalar silently specialized as polynomial"
  unless (readRow r 2 (.list [v,v])).isOk do throwError "valid row rejected"
  if (readRow r 1 (.list [v,v])).isOk then throwError "row truncated"
  if (readRow r 2 (.list [v,.algebra (.poly s raw)])).isOk then throwError "foreign row entry accepted"
  unless (readRow r 0 (.list [])).isOk do throwError "empty row rejected"
  for kind in Contracts.all do
    unless (Contracts.Kind.parse kind.name) == some kind do throwError "schema name did not round trip"
    unless (Contracts.describe kind).limitations.length == 4 do throwError "a contract lost explicit boundaries"
  unless Contracts.Kind.parse "arbitraryPredicate" == none do throwError "unknown schema accepted"
  logInfo "INTENT_VIEWS_COMPLETE: dimensions, duplicates, ring identity and explicit schema boundaries"

example : coefficient [(1,[1]),(2,[1])] [1] = 3 := by decide +kernel
example : coefficient [(1,[1]),(-1,[1])] [1] = 0 := by decide +kernel

-- The same data must survive all three admitted row classes, including zero
-- polynomials, duplicate exponents, rational coefficients and zero-length rows.
run_cmd do
  let r : RingInfo := ⟨0,["x","y"]⟩
  let s : RingInfo := ⟨1,["x","y"]⟩
  let raws : List Raw := [[],[(mkRat 1 2,[2,0]),(mkRat 1 3,[2,0])],[(3,[0,1])]]
  for data in [[],raws] do
    let values := data.map fun p => Value.algebra (.poly r p)
    for presentation in [Value.list values,Value.sequence values,Value.algebra (.row r data)] do
      let .ok row := readRow r data.length presentation | throwError "supported row class rejected"
      unless row.values.map Polynomial.raw == data do throwError "row view changed an entry"
      let .ok listBack := readRow r data.length row.value | throwError "list roundtrip rejected"
      let .ok sequenceBack := readRow r data.length row.sequenceValue | throwError "sequence roundtrip rejected"
      unless listBack.values.map Polynomial.raw == data && sequenceBack.values.map Polynomial.raw == data do
        throwError "row roundtrip lost data"
      for wrongLength in [data.length+1,data.length+2] do
        if (readRow r wrongLength presentation).isOk then throwError "wrong row length accepted"
    if (readRow s data.length (.algebra (.row r data))).isOk then
      throwError "foreign generator row accepted, including the empty row"
  for presentation in [Value.list [.algebra (.poly r [(1,[1])])],
      Value.sequence [.algebra (.poly r [(1,[1])])],Value.algebra (.row r [[(1,[1])]])] do
    if (readRow r 1 presentation).isOk then throwError "malformed exponent accepted through row decoder"
  logInfo "INTENT_ROW_ROUNDTRIPS_COMPLETE: list, sequence, generator-row, empty and malformed data"

-- Explicit convolution examples do not use production polynomial multiplication.
-- p = x + 2y - x and q = 3x - 1, so pq = 6xy - 2y.
run_cmd do
  let r : RingInfo := ⟨0,["x","y"]⟩
  let .ok p := readPolynomial r (.algebra (.poly r [(1,[1,0]),(2,[0,1]),(-1,[1,0])]))
    | throwError "convolution fixture p failed"
  let .ok q := readPolynomial r (.algebra (.poly r [(3,[1,0]),(-1,[0,0])]))
    | throwError "convolution fixture q failed"
  for (powers,expected) in [([1,1],(6 : Rat)),([0,1],-2),([2,0],0),([0,0],0),([2,1],0)] do
    unless productCoefficient p q powers == expected do throwError "wrong convolution coefficient"
    unless productCoefficient q p powers == expected do throwError "product view depends on operand order"
    unless linearCoefficient [p,q] [q,p] powers == 2*expected do throwError "coefficient row lost a summand"
  let k : RingInfo := ⟨2,[]⟩
  let .ok a := readPolynomial k (.algebra (.poly k [(mkRat 1 2,[])]))
    | throwError "zero-variable fixture failed"
  unless productCoefficient a a [] == mkRat 1 4 do throwError "zero-variable coefficient is not exact"
  logInfo "INTENT_VIEW_CONVOLUTION_COMPLETE: duplicate cancellation, both orders, row summation and zero variables"

end Macaulean.M2.Verification.Tests
