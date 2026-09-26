import Macaulean.Interpreter.Check

/-! Native reference observations, replaced by assertions as the collection implementation lands. -/
open Lean Elab Command Macaulean.M2

run_cmd do
  let m2 ← Macaulean.globalM2Server
  for source in #[
    "{}", "{1,2}", "()", "(1)", "(1,)", "(,1)", "(,)", "{,}", "{1,}", "{,1}",
    "1,2,3", "((1,2),3)", "(1,(2,3))", "{(1,2)}", "{1..3}", "{1;2}", "{1;}",
    "{if true then 1 else 2,3}", "if true then 1 else 2,3", "1:7", "0:7", "(-1):7",
    "collectionProbe = 0; 3:(collectionProbe = collectionProbe + 1)",
    "collectionProbe = 0; 0:(collectionProbe = collectionProbe + 1); collectionProbe",
    "{10,20,30}#-1", "(10,20,30)#-1", "{10,20,30}#?(-1)", "(10,20,30)#?(-1)",
    "{10,20,30}#?(-3)", "{10,20,30}#?(-4)", "{10,20,30}#?3", "{10,20,30}#3",
    "{10,20,30}#(1/1)", "{1} == {1/1}", "(1,2) == (1/1,2)", "{true} == {1}",
    "{null} == {null}", "{1,2} == (1,2)", "{1} == 1", "1 == {1}",
    "{1} != {1/1}", "{1,2} | {3}", "(1,2) | (3,4)", "{1} | (2,3)",
    "{1,2} + {3,4}", "{1,2} == {1}", "{1} < {2}", "(1,2) < (1,3)",
    "# {1,2} ^ 2", "# {{1,2},{3}} # 0", "1..1", "2..1", "1..<1",
    "{(1;2),3}", "(1;2,3)", "(1,2;3)", "{1,2;}"
  ] do
    let reply : List String ← m2.sendRequest "evalValue" [source]
    logInfo m!"COLLECTION_REFERENCE {repr source}: {repr reply}"
