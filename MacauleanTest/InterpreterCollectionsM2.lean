import Macaulean.Interpreter.Check
import MacauleanTest.CollectionCases

/-!
# Independent native-M2 collection regressions

Successes require the native oracle, pure interpreter, and explicit expected data
to agree. The wire decoder is not the grammar under test. Separate controls check
runtime failure. Native source is self-contained when it uses assignments.
-/
open Lean Elab Command Macaulean.M2

run_cmd do
  for (source, expected) in CollectionCases.successes do
    let .ok actual := run source | throwError "pure interpreter rejected {repr source}"
    unless actual == expected do
      throwError "wrong pure result for {repr source}: {repr actual}; expected {repr expected}"
    match ← queryM2 source with
    | .ok (.ok native) =>
      unless native == expected do
        throwError "native discrepancy for {repr source}: {repr native}; expected {repr expected}"
    | .ok .error => throwError "native M2 rejected positive case {repr source}"
    | .error message => throwError "native value decoding failed for {repr source}: {message}"
  logInfo m!"COLLECTION_SUCCESSES: {CollectionCases.successes.length} independently checked typed values"

run_cmd do
  for (source, expected) in CollectionCases.errors do
    unless run source == .error expected do throwError "wrong interpreter error for {repr source}"
    let reply ← queryM2 source
    unless reply == .ok .error do
      throwError "native M2 unexpectedly accepted error control {repr source}"
  logInfo m!"COLLECTION_ERRORS: {CollectionCases.errors.length} independent runtime-error controls"

-- A grid checks range endpoint arithmetic and both positive/negative indexing.
run_cmd do
  for first in ([-3, -1, 0, 2, 4] : List Int) do
    for last in ([-3, -1, 0, 2, 4] : List Int) do
      for op in ["..", "..<"] do
        let source := s!"({first}){op}({last})"
        let .ok expected := run source | throwError "range rejected"
        let .ok (.ok native) ← queryM2 source | throwError "native range failed"
        unless native == expected do throwError "range mismatch for {source}"
  for container in ["{10,20,30}", "(10,20,30)", "{}", "()"] do
    for i in ([-5, -3, -2, -1, 0, 1, 2, 3, 5] : List Int) do
      let sourceExists := s!"{container}#?({i})"
      let .ok expected := run sourceExists | throwError "existence check rejected"
      let .ok (.ok native) ← queryM2 sourceExists | throwError "native existence check failed"
      unless native == expected do throwError "index-existence mismatch: {sourceExists}"
      if expected == .bool true then
        let source := s!"{container}#({i})"
        let .ok expected := run source | throwError "in-bounds index rejected"
        let .ok (.ok native) ← queryM2 source | throwError "native in-bounds index failed"
        unless native == expected do throwError "index mismatch: {source}"
  logInfo "COLLECTION_GRIDS: 50 ranges, 36 index-existence queries, 12 successful accesses"

-- Kernel-check the reified collection result through the real certificate path.
run_cmd do
  let source := "{1/1, (2, null), {}, (), 1:(3/4)}"
  let outcome := run source
  let .ok _ := outcome | throwError "certificate fixture failed"
  let .ok reply ← queryM2 source | throwError "certificate oracle failed"
  unless agrees outcome reply do throwError "certificate oracle disagreed"
  addRunTheorem `collectionCertificate source outcome "Nested collection certificate regression."

example : run "{1/1, (2, null), {}, (), 1:(3/4)}" = .ok
    (.list [.qq (mkRat 1 1), .sequence [.zz 2, .null], .list [], .sequence [],
      .sequence [.qq (mkRat 3 4)]]) := collectionCertificate

-- Check the native concrete tree rather than guessing association from values.
run_cmd do
  for (source, predicate) in #[
    ("a,b,c", "toString(t#0) == \"Binary\" and toString(t#1#0) == \"Binary\" and toString(t#2#1) == \",\""),
    ("a|b|c", "toString(t#1#0) == \"Binary\" and toString(t#2#1) == \"|\""),
    ("a:b:c", "toString(t#3#0) == \"Binary\" and toString(t#2#1) == \":\""),
    ("1..3+4", "toString(t#2#1) == \"..\" and toString(t#3#2#1) == \"+\""),
    ("#a#0", "toString(t#0) == \"Unary\" and toString(t#1#1) == \"#\" and toString(t#2#2#1) == \"#\""),
    ("a=1,2", "toString(t#2#1) == \",\" and toString(t#1#2#1) == \"=\"")
  ] do
    let quoted := (Json.str source).compress
    let probe := s!"(t := (parse {quoted})#0; {predicate})"
    match ← queryM2 probe with
    | .ok (.ok (.bool true)) => pure ()
    | .ok reply => throwError "native parser shape disagrees for {repr source}: {reply.toM2String}"
    | .error message => throwError "native parser probe failed: {message}"
  logInfo "COLLECTION_PARSE_SHAPES: 6 native structural checks"

-- The transport retains types that source printers sometimes omit.
run_cmd do
  let m2 ← globalM2Server
  let payload : List String ← m2.sendRequest "evalValueTree" ["{1/1,1:(),null}"]
  unless payload == ["ok", "List", "3", "QQ", "1", "1", "Sequence", "1", "Sequence", "0", "Nothing"] do
    throwError "typed wire erased nested classes: {repr payload}"
  let unsupported : List String ← m2.sendRequest "evalValueTree" ["\"not a scalar\""]
  if (M2Reply.ofWire unsupported).isOk then throwError "wire decoder accepted an unsupported native class"
