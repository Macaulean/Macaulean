import Macaulean.Verification.Snapshot

namespace Macaulean.M2.Verification.GraphTests
open Lean Elab Command
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

/-- This has exponentially many nodes when naively expanded as a tree. -/
private def shared : Nat → Expr
  | 0 => toExpr (1 : Nat)
  | n+1 => let child := shared n; mkApp2 (mkConst ``Nat.add) child child

run_cmd do
  let encoded := ExpressionGraph.encodeMany [shared 30]
  unless encoded.nodeCount < 100 do throwError "shared expression was expanded instead of interned"
  unless encoded.constants.contains ``Nat.add do throwError "DAG encoding omitted a constant dependency"
  let a := mkLambda `a .default (mkConst ``Nat) (mkBVar 0)
  let b := mkLambda `renamed .default (mkConst ``Nat) (mkBVar 0)
  unless Snapshot.exprKey a == Snapshot.exprKey b do throwError "binder names changed semantic identity"
  unless Snapshot.exprKey a != Snapshot.exprKey (mkLambda `a .implicit (mkConst ``Nat) (mkBVar 0)) do
    throwError "binder modes were erased"
  unless Snapshot.exprKey (shared 29) != Snapshot.exprKey (shared 30) do throwError "different expression graphs collided"
  let reused := mkApp2 (mkConst ``Nat.add) a a
  let copied := mkApp2 (mkConst ``Nat.add) a b
  unless Snapshot.exprKey reused == Snapshot.exprKey copied do
    throwError "encoding depends on allocation or alpha-equivalent sharing"
  unless Snapshot.exprKey (mkConst ``List [.zero]) != Snapshot.exprKey (mkConst ``List [.succ .zero]) do
    throwError "universe arguments were omitted"
  let first := Snapshot.sealTheory (← getEnv) [``Nat.add,``Nat.add]
  let second := Snapshot.sealTheory (← getEnv) [``Nat.add]
  let .ok first := first | throwError "duplicate root manifest failed"
  let .ok second := second | throwError "root manifest failed"
  unless first.payload == second.payload do throwError "duplicate dependency roots changed manifest"
  unless first.declarations.length == first.declarations.eraseDups.length do
    throwError "manifest repeats dependency declarations"
  logInfo s!"INTENT_EXPRESSION_GRAPH_COMPLETE: shared depth 30 uses {encoded.nodeCount} nodes; alpha identity, modes, universes and complete dependencies checked"

end Macaulean.M2.Verification.GraphTests
