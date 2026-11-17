import Macaulean.Verification.Handles.Attr
import Macaulean.Verification.Handles.Intro

/-!
# Type-directed reduction of production operators

M2 syntax already uses a single `BinOp.add` for every operand type. Handle
expansion reduces that same production dispatch table rather than maintaining a
second table of per-type arithmetic lemmas. Only dispatch definitions unfold;
symbolic mathematical operations and polynomial implementation details stay intact.
-/
namespace Macaulean.M2.Handles
open Lean Meta

/-- Unfold only the runtime's operator dispatch, keeping the resulting Lean
arithmetic symbolic. The returned expression is definitionally equal to the input. -/
private def reduceOperator (e : Expr) : MetaM Expr := do
  let mut thms : SimpTheorems := {}
  for name in [``evalBinOp, ``evalUnOp, ``Value.toRat?, ``ratZPow] do
    thms ← thms.addDeclToUnfold name
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
  return (← Meta.dsimp e ctx).1

/-- Unknown call results remain opaque, so modular `m2_use` goals stay small. -/
private def knownConstructor (e : Expr) : MetaM Bool := do
  return (← isConstructorApp? e).isSome

/-- Arithmetic uses the runtime's existing dispatch across all operand kinds.
Collection operations keep their bounds-aware mathematical simplification rules. -/
dsimproc [m2_simp] reduceBinaryOperator (evalBinOp _ _ _) := fun e => do
  let_expr evalBinOp op a b := e | return .continue
  let some opName := op.getAppFn.constName? | return .continue
  unless [``BinOp.add, ``BinOp.sub, ``BinOp.mul, ``BinOp.div,
      ``BinOp.quot, ``BinOp.rem, ``BinOp.pow, ``BinOp.eq, ``BinOp.ne,
      ``BinOp.lt, ``BinOp.le, ``BinOp.gt, ``BinOp.ge].contains opName do
    return .continue
  unless (← knownConstructor a) && (← knownConstructor b) do return .continue
  let result ← reduceOperator e
  if result == e then return .continue
  return .visit result

dsimproc [m2_simp] reduceUnaryOperator (evalUnOp _ _) := fun e => do
  let_expr evalUnOp op a := e | return .continue
  let some opName := op.getAppFn.constName? | return .continue
  unless [``UnOp.neg, ``UnOp.pos].contains opName do return .continue
  unless ← knownConstructor a do return .continue
  let result ← reduceOperator e
  if result == e then return .continue
  return .visit result

end Macaulean.M2.Handles
